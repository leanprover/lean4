// Lean compiler output
// Module: Lean.Elab.App
// Imports: Init Lean.Util.FindMVar Lean.Elab.Term Lean.Elab.Binders
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
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_App_7__hasOnlyTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind;
extern lean_object* l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
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
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___closed__3;
lean_object* l___private_Lean_Elab_App_9__nextArgIsHole___boxed(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__toMessageData___closed__1;
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_14__resolveLValLoop___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__3;
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_21__elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__6;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__7;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Term_throwError___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__7;
lean_object* l___private_Lean_Elab_App_5__getForallBody(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
uint8_t l___private_Lean_Elab_App_9__nextArgIsHole(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__17;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object*);
lean_object* l___private_Lean_Elab_App_23__toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__8;
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
lean_object* l_Lean_Elab_getRefPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__9;
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Elab_App_23__toMessageData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__27;
lean_object* l___private_Lean_Elab_App_26__expandApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isTypeFormer(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__4;
lean_object* l___private_Lean_Elab_App_17__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_App_20__elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawIdent(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__2;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__3;
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
extern lean_object* l_Lean_Format_repr___main___closed__13;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__3;
lean_object* l___private_Lean_Elab_App_21__elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__8;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__1;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
lean_object* l___private_Lean_Elab_App_6__hasTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13;
uint8_t l___private_Lean_Elab_App_7__hasOnlyTypeMVar(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_App_25__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__4;
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__7;
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited;
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__9;
extern lean_object* l___private_Lean_Syntax_6__formatInfo___closed__1;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__6;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_5__getForallBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__6;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceInfo___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__7;
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_17__addLValArg___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_App_12__throwLValError(lean_object*);
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__22;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object*);
lean_object* l_Lean_Elab_Term_elabAtom(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Lean_Elab_getRefPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_6__hasTypeMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__10;
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
lean_object* l_Lean_Elab_Term_elabIdent(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__11;
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__3;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__1;
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
extern lean_object* l_Lean_importModules___closed__1;
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main___closed__1;
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l___private_Lean_Elab_App_15__resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
lean_object* l_List_map___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__1(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__12;
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_27__regTraceClasses(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofArray(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_17__addLValArg___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__16;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2;
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppFnId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__elabAppAux___closed__2;
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__10;
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__elabAppAux___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__20;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__2;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__getSuccess(lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__10;
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_26__expandApp(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__11;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__19;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData___main(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___closed__1;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_3__mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__11;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__1;
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawIdent___closed__1;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
extern lean_object* l_Lean_Meta_Exception_toStr___closed__6;
uint8_t l_Lean_Position_DecidableEq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
extern lean_object* l_Lean_Format_repr___main___closed__16;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__12;
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_25__elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l___private_Lean_Elab_App_17__addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___closed__1;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_22__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__2;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7;
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
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
x_3 = l_Lean_Name_toString___closed__1;
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
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_1, x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_array_push(x_1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_10);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Elab_Term_addNamedArg___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_Term_addNamedArg___closed__6;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Term_throwError___rarg(x_18, x_3, x_4);
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
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_3);
lean_inc(x_9);
x_10 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
lean_inc(x_3);
x_15 = l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(x_9, x_14, x_3, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_2 = x_18;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_2 = x_22;
x_4 = x_20;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Term_inferType(x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = l_Lean_Elab_Term_ensureHasTypeAux(x_9, x_7, x_2, x_10, x_4, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Elab_App_2__elabArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = 1;
lean_inc(x_4);
x_9 = l_Lean_Elab_Term_elabTerm(x_6, x_7, x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_App_1__ensureArgType(x_1, x_10, x_3, x_4, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l___private_Lean_Elab_App_1__ensureArgType(x_1, x_17, x_3, x_4, x_5);
return x_18;
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
lean_object* l___private_Lean_Elab_App_4__tryCoeFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_mkFreshLevelMVar(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
x_8 = l_Lean_mkSort(x_6);
lean_inc(x_1);
x_9 = l___private_Lean_Elab_App_3__mkArrow(x_1, x_8, x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = 0;
x_14 = lean_box(0);
lean_inc(x_3);
x_15 = l_Lean_Elab_Term_mkFreshExprMVar(x_12, x_13, x_14, x_3, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Elab_Term_getLevel(x_1, x_3, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_App_4__tryCoeFun___closed__2;
lean_inc(x_23);
x_25 = l_Lean_mkConst(x_24, x_23);
x_26 = l_Lean_mkAppStx___closed__9;
lean_inc(x_1);
x_27 = lean_array_push(x_26, x_1);
lean_inc(x_16);
x_28 = lean_array_push(x_27, x_16);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_28, x_28, x_29, x_25);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = 1;
lean_inc(x_3);
x_33 = l_Lean_Elab_Term_mkFreshExprMVar(x_31, x_32, x_14, x_3, x_20);
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
x_51 = l_Lean_Expr_mvarId_x21(x_34);
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 4);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 7);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 8);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_63 = lean_ctor_get(x_3, 9);
lean_inc(x_63);
x_64 = 0;
x_65 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_53);
lean_ctor_set(x_65, 2, x_54);
lean_ctor_set(x_65, 3, x_55);
lean_ctor_set(x_65, 4, x_56);
lean_ctor_set(x_65, 5, x_57);
lean_ctor_set(x_65, 6, x_58);
lean_ctor_set(x_65, 7, x_59);
lean_ctor_set(x_65, 8, x_60);
lean_ctor_set(x_65, 9, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*10, x_61);
lean_ctor_set_uint8(x_65, sizeof(void*)*10 + 1, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*10 + 2, x_64);
x_66 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_51, x_65, x_35);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_37 = x_69;
x_38 = x_68;
goto block_50;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_70, 0);
lean_inc(x_80);
lean_dec(x_70);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 4);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l___private_Lean_Elab_App_4__tryCoeFun___closed__7;
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Elab_Term_throwError___rarg(x_84, x_3, x_71);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_72 = x_90;
goto block_79;
}
}
else
{
lean_object* x_91; 
x_91 = lean_box(0);
x_72 = x_91;
goto block_79;
}
block_79:
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_72);
x_73 = l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
x_74 = l_Lean_Elab_Term_throwError___rarg(x_73, x_3, x_71);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
return x_74;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
block_50:
{
if (x_37 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_39 = l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
x_40 = l_Lean_Elab_Term_throwError___rarg(x_39, x_3, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
x_41 = l___private_Lean_Elab_App_4__tryCoeFun___closed__6;
x_42 = l_Lean_mkConst(x_41, x_23);
x_43 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_44 = lean_array_push(x_43, x_1);
x_45 = lean_array_push(x_44, x_16);
x_46 = lean_array_push(x_45, x_2);
x_47 = lean_array_push(x_46, x_34);
x_48 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_47, x_47, x_29, x_42);
lean_dec(x_47);
if (lean_is_scalar(x_36)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_36;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_38);
return x_49;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_18);
if (x_92 == 0)
{
return x_18;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_18, 0);
x_94 = lean_ctor_get(x_18, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_18);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
x_9 = l_Array_isEmpty___rarg(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_3, 9);
x_16 = l_Lean_Elab_replaceRef(x_7, x_15);
lean_dec(x_15);
lean_dec(x_7);
lean_ctor_set(x_3, 9, x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_nat_sub(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
x_22 = l___private_Lean_Elab_App_5__getForallBody___main(x_20, x_21, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_13);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_Expr_hasLooseBVars(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l___private_Lean_Elab_App_6__hasTypeMVar(x_1, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_13);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = l___private_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_25);
lean_dec(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_13);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Elab_Term_isDefEq(x_13, x_25, x_3, x_4);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_13);
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_4);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
x_48 = lean_ctor_get(x_3, 2);
x_49 = lean_ctor_get(x_3, 3);
x_50 = lean_ctor_get(x_3, 4);
x_51 = lean_ctor_get(x_3, 5);
x_52 = lean_ctor_get(x_3, 6);
x_53 = lean_ctor_get(x_3, 7);
x_54 = lean_ctor_get(x_3, 8);
x_55 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_56 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_57 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_58 = lean_ctor_get(x_3, 9);
lean_inc(x_58);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
x_59 = l_Lean_Elab_replaceRef(x_7, x_58);
lean_dec(x_58);
lean_dec(x_7);
x_60 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_47);
lean_ctor_set(x_60, 2, x_48);
lean_ctor_set(x_60, 3, x_49);
lean_ctor_set(x_60, 4, x_50);
lean_ctor_set(x_60, 5, x_51);
lean_ctor_set(x_60, 6, x_52);
lean_ctor_set(x_60, 7, x_53);
lean_ctor_set(x_60, 8, x_54);
lean_ctor_set(x_60, 9, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*10, x_55);
lean_ctor_set_uint8(x_60, sizeof(void*)*10 + 1, x_56);
lean_ctor_set_uint8(x_60, sizeof(void*)*10 + 2, x_57);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
x_62 = lean_array_get_size(x_61);
lean_dec(x_61);
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
x_64 = lean_nat_sub(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
x_65 = lean_ctor_get(x_1, 4);
lean_inc(x_65);
x_66 = l___private_Lean_Elab_App_5__getForallBody___main(x_64, x_65, x_2);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
lean_dec(x_13);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_4);
return x_68;
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_Expr_hasLooseBVars(x_69);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l___private_Lean_Elab_App_6__hasTypeMVar(x_1, x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_13);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_4);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = l___private_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_69);
lean_dec(x_1);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_13);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_4);
return x_76;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_Elab_Term_isDefEq(x_13, x_69, x_60, x_4);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_13);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_4);
return x_87;
}
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_4);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_4);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_4);
return x_93;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
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
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_47; 
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_16 = lean_ctor_get(x_4, 9);
x_17 = l_Lean_Elab_replaceRef(x_6, x_16);
lean_dec(x_16);
lean_ctor_set(x_4, 9, x_17);
lean_inc(x_4);
lean_inc(x_3);
x_47 = l_Lean_Elab_Term_whnfForall(x_3, x_4, x_5);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 7)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint64_t x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_48, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_48, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_48, 2);
lean_inc(x_95);
x_96 = lean_ctor_get_uint64(x_48, sizeof(void*)*3);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_93, x_11, x_97);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; lean_object* x_100; 
x_99 = (uint8_t)((x_96 << 24) >> 61);
x_100 = lean_box(x_99);
switch (lean_obj_tag(x_100)) {
case 1:
{
if (x_9 == 0)
{
uint8_t x_101; 
lean_dec(x_93);
lean_dec(x_48);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_1);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_102 = lean_ctor_get(x_1, 6);
lean_dec(x_102);
x_103 = lean_ctor_get(x_1, 5);
lean_dec(x_103);
x_104 = lean_ctor_get(x_1, 4);
lean_dec(x_104);
x_105 = lean_ctor_get(x_1, 3);
lean_dec(x_105);
x_106 = lean_ctor_get(x_1, 2);
lean_dec(x_106);
x_107 = lean_ctor_get(x_1, 1);
lean_dec(x_107);
x_108 = lean_ctor_get(x_1, 0);
lean_dec(x_108);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_94);
x_110 = 0;
x_111 = lean_box(0);
lean_inc(x_4);
x_112 = l_Lean_Elab_Term_mkFreshExprMVar(x_109, x_110, x_111, x_4, x_49);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_4);
lean_inc(x_113);
x_115 = l_Lean_Elab_Term_isTypeFormer(x_113, x_4, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_113);
x_119 = l_Lean_mkApp(x_2, x_113);
x_120 = lean_expr_instantiate1(x_95, x_113);
lean_dec(x_113);
lean_dec(x_95);
x_2 = x_119;
x_3 = x_120;
x_5 = x_118;
goto _start;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_115, 1);
lean_inc(x_122);
lean_dec(x_115);
x_123 = l_Lean_Expr_mvarId_x21(x_113);
x_124 = lean_array_push(x_13, x_123);
lean_ctor_set(x_1, 6, x_124);
lean_inc(x_113);
x_125 = l_Lean_mkApp(x_2, x_113);
x_126 = lean_expr_instantiate1(x_95, x_113);
lean_dec(x_113);
lean_dec(x_95);
x_2 = x_125;
x_3 = x_126;
x_5 = x_122;
goto _start;
}
}
else
{
uint8_t x_128; 
lean_dec(x_113);
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_115);
if (x_128 == 0)
{
return x_115;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_115, 0);
x_130 = lean_ctor_get(x_115, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_115);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_1);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_94);
x_133 = 0;
x_134 = lean_box(0);
lean_inc(x_4);
x_135 = l_Lean_Elab_Term_mkFreshExprMVar(x_132, x_133, x_134, x_4, x_49);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_4);
lean_inc(x_136);
x_138 = l_Lean_Elab_Term_isTypeFormer(x_136, x_4, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_142, 0, x_6);
lean_ctor_set(x_142, 1, x_7);
lean_ctor_set(x_142, 2, x_8);
lean_ctor_set(x_142, 3, x_10);
lean_ctor_set(x_142, 4, x_11);
lean_ctor_set(x_142, 5, x_12);
lean_ctor_set(x_142, 6, x_13);
lean_ctor_set_uint8(x_142, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 1, x_15);
lean_inc(x_136);
x_143 = l_Lean_mkApp(x_2, x_136);
x_144 = lean_expr_instantiate1(x_95, x_136);
lean_dec(x_136);
lean_dec(x_95);
x_1 = x_142;
x_2 = x_143;
x_3 = x_144;
x_5 = x_141;
goto _start;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_138, 1);
lean_inc(x_146);
lean_dec(x_138);
x_147 = l_Lean_Expr_mvarId_x21(x_136);
x_148 = lean_array_push(x_13, x_147);
x_149 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_149, 0, x_6);
lean_ctor_set(x_149, 1, x_7);
lean_ctor_set(x_149, 2, x_8);
lean_ctor_set(x_149, 3, x_10);
lean_ctor_set(x_149, 4, x_11);
lean_ctor_set(x_149, 5, x_12);
lean_ctor_set(x_149, 6, x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_149, sizeof(void*)*7 + 1, x_15);
lean_inc(x_136);
x_150 = l_Lean_mkApp(x_2, x_136);
x_151 = lean_expr_instantiate1(x_95, x_136);
lean_dec(x_136);
lean_dec(x_95);
x_1 = x_149;
x_2 = x_150;
x_3 = x_151;
x_5 = x_146;
goto _start;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_136);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_153 = lean_ctor_get(x_138, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_138, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_155 = x_138;
} else {
 lean_dec_ref(x_138);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
else
{
lean_object* x_157; uint8_t x_158; 
lean_inc(x_4);
lean_inc(x_1);
x_157 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_48, x_4, x_49);
x_158 = !lean_is_exclusive(x_1);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_1, 6);
lean_dec(x_159);
x_160 = lean_ctor_get(x_1, 5);
lean_dec(x_160);
x_161 = lean_ctor_get(x_1, 4);
lean_dec(x_161);
x_162 = lean_ctor_get(x_1, 3);
lean_dec(x_162);
x_163 = lean_ctor_get(x_1, 2);
lean_dec(x_163);
x_164 = lean_ctor_get(x_1, 1);
lean_dec(x_164);
x_165 = lean_ctor_get(x_1, 0);
lean_dec(x_165);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_157, 1);
lean_inc(x_166);
lean_dec(x_157);
x_167 = lean_array_get_size(x_7);
x_168 = lean_nat_dec_lt(x_10, x_167);
lean_dec(x_167);
if (x_168 == 0)
{
uint8_t x_169; 
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_169 = l_Array_isEmpty___rarg(x_11);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_170 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_170, 0, x_93);
x_171 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_172 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_174 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = x_11;
x_176 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_175);
x_177 = x_176;
x_178 = l_Array_toList___rarg(x_177);
lean_dec(x_177);
x_179 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_178);
x_180 = l_Array_HasRepr___rarg___closed__1;
x_181 = lean_string_append(x_180, x_179);
lean_dec(x_179);
x_182 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_184 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_184, 0, x_174);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_Elab_Term_throwError___rarg(x_184, x_4, x_166);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
lean_dec(x_93);
lean_dec(x_11);
x_186 = l_Lean_Elab_Term_getOptions(x_4, x_166);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_190 = l_Lean_checkTraceOption(x_187, x_189);
lean_dec(x_187);
if (x_190 == 0)
{
x_18 = x_188;
goto block_46;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_inc(x_2);
x_191 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_191, 0, x_2);
x_192 = l_Lean_Elab_Term_logTrace(x_189, x_191, x_4, x_188);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_18 = x_193;
goto block_46;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_93);
lean_dec(x_3);
x_194 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_195 = l___private_Lean_Elab_App_2__elabArg(x_2, x_194, x_94, x_4, x_166);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_add(x_10, x_198);
lean_dec(x_10);
x_200 = 1;
lean_ctor_set(x_1, 3, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_200);
lean_inc(x_196);
x_201 = l_Lean_mkApp(x_2, x_196);
x_202 = lean_expr_instantiate1(x_95, x_196);
lean_dec(x_196);
lean_dec(x_95);
x_2 = x_201;
x_3 = x_202;
x_5 = x_197;
goto _start;
}
else
{
uint8_t x_204; 
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_204 = !lean_is_exclusive(x_195);
if (x_204 == 0)
{
return x_195;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_195, 0);
x_206 = lean_ctor_get(x_195, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_195);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_208 = !lean_is_exclusive(x_157);
if (x_208 == 0)
{
return x_157;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_157, 0);
x_210 = lean_ctor_get(x_157, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_157);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_212 = lean_ctor_get(x_157, 1);
lean_inc(x_212);
lean_dec(x_157);
x_213 = lean_array_get_size(x_7);
x_214 = lean_nat_dec_lt(x_10, x_213);
lean_dec(x_213);
if (x_214 == 0)
{
uint8_t x_215; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_215 = l_Array_isEmpty___rarg(x_11);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_216 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_216, 0, x_93);
x_217 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_218 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_220 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = x_11;
x_222 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_221);
x_223 = x_222;
x_224 = l_Array_toList___rarg(x_223);
lean_dec(x_223);
x_225 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_224);
x_226 = l_Array_HasRepr___rarg___closed__1;
x_227 = lean_string_append(x_226, x_225);
lean_dec(x_225);
x_228 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_230 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_230, 0, x_220);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Lean_Elab_Term_throwError___rarg(x_230, x_4, x_212);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
lean_dec(x_93);
lean_dec(x_11);
x_232 = l_Lean_Elab_Term_getOptions(x_4, x_212);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_236 = l_Lean_checkTraceOption(x_233, x_235);
lean_dec(x_233);
if (x_236 == 0)
{
x_18 = x_234;
goto block_46;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_inc(x_2);
x_237 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_237, 0, x_2);
x_238 = l_Lean_Elab_Term_logTrace(x_235, x_237, x_4, x_234);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_18 = x_239;
goto block_46;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_93);
lean_dec(x_3);
x_240 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_241 = l___private_Lean_Elab_App_2__elabArg(x_2, x_240, x_94, x_4, x_212);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_unsigned_to_nat(1u);
x_245 = lean_nat_add(x_10, x_244);
lean_dec(x_10);
x_246 = 1;
x_247 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_247, 0, x_6);
lean_ctor_set(x_247, 1, x_7);
lean_ctor_set(x_247, 2, x_8);
lean_ctor_set(x_247, 3, x_245);
lean_ctor_set(x_247, 4, x_11);
lean_ctor_set(x_247, 5, x_12);
lean_ctor_set(x_247, 6, x_13);
lean_ctor_set_uint8(x_247, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_247, sizeof(void*)*7 + 1, x_246);
lean_inc(x_242);
x_248 = l_Lean_mkApp(x_2, x_242);
x_249 = lean_expr_instantiate1(x_95, x_242);
lean_dec(x_242);
lean_dec(x_95);
x_1 = x_247;
x_2 = x_248;
x_3 = x_249;
x_5 = x_243;
goto _start;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_251 = lean_ctor_get(x_241, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_241, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_253 = x_241;
} else {
 lean_dec_ref(x_241);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_255 = lean_ctor_get(x_157, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_157, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_257 = x_157;
} else {
 lean_dec_ref(x_157);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
}
}
case 3:
{
if (x_9 == 0)
{
uint8_t x_259; 
lean_dec(x_93);
lean_dec(x_48);
lean_dec(x_3);
x_259 = !lean_is_exclusive(x_1);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_260 = lean_ctor_get(x_1, 6);
lean_dec(x_260);
x_261 = lean_ctor_get(x_1, 5);
lean_dec(x_261);
x_262 = lean_ctor_get(x_1, 4);
lean_dec(x_262);
x_263 = lean_ctor_get(x_1, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_1, 2);
lean_dec(x_264);
x_265 = lean_ctor_get(x_1, 1);
lean_dec(x_265);
x_266 = lean_ctor_get(x_1, 0);
lean_dec(x_266);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_94);
x_268 = 1;
x_269 = lean_box(0);
lean_inc(x_4);
x_270 = l_Lean_Elab_Term_mkFreshExprMVar(x_267, x_268, x_269, x_4, x_49);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l_Lean_Expr_mvarId_x21(x_271);
x_274 = lean_array_push(x_12, x_273);
lean_ctor_set(x_1, 5, x_274);
lean_inc(x_271);
x_275 = l_Lean_mkApp(x_2, x_271);
x_276 = lean_expr_instantiate1(x_95, x_271);
lean_dec(x_271);
lean_dec(x_95);
x_2 = x_275;
x_3 = x_276;
x_5 = x_272;
goto _start;
}
else
{
lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_1);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_94);
x_279 = 1;
x_280 = lean_box(0);
lean_inc(x_4);
x_281 = l_Lean_Elab_Term_mkFreshExprMVar(x_278, x_279, x_280, x_4, x_49);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = l_Lean_Expr_mvarId_x21(x_282);
x_285 = lean_array_push(x_12, x_284);
x_286 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_286, 0, x_6);
lean_ctor_set(x_286, 1, x_7);
lean_ctor_set(x_286, 2, x_8);
lean_ctor_set(x_286, 3, x_10);
lean_ctor_set(x_286, 4, x_11);
lean_ctor_set(x_286, 5, x_285);
lean_ctor_set(x_286, 6, x_13);
lean_ctor_set_uint8(x_286, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_286, sizeof(void*)*7 + 1, x_15);
lean_inc(x_282);
x_287 = l_Lean_mkApp(x_2, x_282);
x_288 = lean_expr_instantiate1(x_95, x_282);
lean_dec(x_282);
lean_dec(x_95);
x_1 = x_286;
x_2 = x_287;
x_3 = x_288;
x_5 = x_283;
goto _start;
}
}
else
{
uint8_t x_290; 
x_290 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; 
lean_inc(x_4);
lean_inc(x_1);
x_291 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_48, x_4, x_49);
x_292 = !lean_is_exclusive(x_1);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_293 = lean_ctor_get(x_1, 6);
lean_dec(x_293);
x_294 = lean_ctor_get(x_1, 5);
lean_dec(x_294);
x_295 = lean_ctor_get(x_1, 4);
lean_dec(x_295);
x_296 = lean_ctor_get(x_1, 3);
lean_dec(x_296);
x_297 = lean_ctor_get(x_1, 2);
lean_dec(x_297);
x_298 = lean_ctor_get(x_1, 1);
lean_dec(x_298);
x_299 = lean_ctor_get(x_1, 0);
lean_dec(x_299);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_291, 1);
lean_inc(x_300);
lean_dec(x_291);
x_301 = lean_array_get_size(x_7);
x_302 = lean_nat_dec_lt(x_10, x_301);
lean_dec(x_301);
if (x_302 == 0)
{
uint8_t x_303; 
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_303 = l_Array_isEmpty___rarg(x_11);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_304 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_304, 0, x_93);
x_305 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_306 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_304);
x_307 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_308 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = x_11;
x_310 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_309);
x_311 = x_310;
x_312 = l_Array_toList___rarg(x_311);
lean_dec(x_311);
x_313 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_312);
x_314 = l_Array_HasRepr___rarg___closed__1;
x_315 = lean_string_append(x_314, x_313);
lean_dec(x_313);
x_316 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_318 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_318, 0, x_308);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_Elab_Term_throwError___rarg(x_318, x_4, x_300);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_93);
lean_dec(x_11);
x_320 = l_Lean_Elab_Term_getOptions(x_4, x_300);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_324 = l_Lean_checkTraceOption(x_321, x_323);
lean_dec(x_321);
if (x_324 == 0)
{
x_18 = x_322;
goto block_46;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_inc(x_2);
x_325 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_325, 0, x_2);
x_326 = l_Lean_Elab_Term_logTrace(x_323, x_325, x_4, x_322);
x_327 = lean_ctor_get(x_326, 1);
lean_inc(x_327);
lean_dec(x_326);
x_18 = x_327;
goto block_46;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_93);
lean_dec(x_3);
x_328 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_329 = l___private_Lean_Elab_App_2__elabArg(x_2, x_328, x_94, x_4, x_300);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_unsigned_to_nat(1u);
x_333 = lean_nat_add(x_10, x_332);
lean_dec(x_10);
x_334 = 1;
lean_ctor_set(x_1, 3, x_333);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_334);
lean_inc(x_330);
x_335 = l_Lean_mkApp(x_2, x_330);
x_336 = lean_expr_instantiate1(x_95, x_330);
lean_dec(x_330);
lean_dec(x_95);
x_2 = x_335;
x_3 = x_336;
x_5 = x_331;
goto _start;
}
else
{
uint8_t x_338; 
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_338 = !lean_is_exclusive(x_329);
if (x_338 == 0)
{
return x_329;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_329, 0);
x_340 = lean_ctor_get(x_329, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_329);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
}
}
else
{
uint8_t x_342; 
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_342 = !lean_is_exclusive(x_291);
if (x_342 == 0)
{
return x_291;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_291, 0);
x_344 = lean_ctor_get(x_291, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_291);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_346 = lean_ctor_get(x_291, 1);
lean_inc(x_346);
lean_dec(x_291);
x_347 = lean_array_get_size(x_7);
x_348 = lean_nat_dec_lt(x_10, x_347);
lean_dec(x_347);
if (x_348 == 0)
{
uint8_t x_349; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_349 = l_Array_isEmpty___rarg(x_11);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_350 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_350, 0, x_93);
x_351 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_352 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_350);
x_353 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_354 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
x_355 = x_11;
x_356 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_355);
x_357 = x_356;
x_358 = l_Array_toList___rarg(x_357);
lean_dec(x_357);
x_359 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_358);
x_360 = l_Array_HasRepr___rarg___closed__1;
x_361 = lean_string_append(x_360, x_359);
lean_dec(x_359);
x_362 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_362, 0, x_361);
x_363 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_363, 0, x_362);
x_364 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_364, 0, x_354);
lean_ctor_set(x_364, 1, x_363);
x_365 = l_Lean_Elab_Term_throwError___rarg(x_364, x_4, x_346);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
lean_dec(x_93);
lean_dec(x_11);
x_366 = l_Lean_Elab_Term_getOptions(x_4, x_346);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_370 = l_Lean_checkTraceOption(x_367, x_369);
lean_dec(x_367);
if (x_370 == 0)
{
x_18 = x_368;
goto block_46;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_inc(x_2);
x_371 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_371, 0, x_2);
x_372 = l_Lean_Elab_Term_logTrace(x_369, x_371, x_4, x_368);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec(x_372);
x_18 = x_373;
goto block_46;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_93);
lean_dec(x_3);
x_374 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_375 = l___private_Lean_Elab_App_2__elabArg(x_2, x_374, x_94, x_4, x_346);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_unsigned_to_nat(1u);
x_379 = lean_nat_add(x_10, x_378);
lean_dec(x_10);
x_380 = 1;
x_381 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_381, 0, x_6);
lean_ctor_set(x_381, 1, x_7);
lean_ctor_set(x_381, 2, x_8);
lean_ctor_set(x_381, 3, x_379);
lean_ctor_set(x_381, 4, x_11);
lean_ctor_set(x_381, 5, x_12);
lean_ctor_set(x_381, 6, x_13);
lean_ctor_set_uint8(x_381, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_381, sizeof(void*)*7 + 1, x_380);
lean_inc(x_376);
x_382 = l_Lean_mkApp(x_2, x_376);
x_383 = lean_expr_instantiate1(x_95, x_376);
lean_dec(x_376);
lean_dec(x_95);
x_1 = x_381;
x_2 = x_382;
x_3 = x_383;
x_5 = x_377;
goto _start;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_385 = lean_ctor_get(x_375, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_375, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_387 = x_375;
} else {
 lean_dec_ref(x_375);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_389 = lean_ctor_get(x_291, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_291, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_391 = x_291;
} else {
 lean_dec_ref(x_291);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_93);
lean_dec(x_48);
lean_dec(x_3);
x_393 = !lean_is_exclusive(x_1);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_394 = lean_ctor_get(x_1, 6);
lean_dec(x_394);
x_395 = lean_ctor_get(x_1, 5);
lean_dec(x_395);
x_396 = lean_ctor_get(x_1, 4);
lean_dec(x_396);
x_397 = lean_ctor_get(x_1, 3);
lean_dec(x_397);
x_398 = lean_ctor_get(x_1, 2);
lean_dec(x_398);
x_399 = lean_ctor_get(x_1, 1);
lean_dec(x_399);
x_400 = lean_ctor_get(x_1, 0);
lean_dec(x_400);
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_94);
x_402 = 1;
x_403 = lean_box(0);
lean_inc(x_4);
x_404 = l_Lean_Elab_Term_mkFreshExprMVar(x_401, x_402, x_403, x_4, x_49);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_unsigned_to_nat(1u);
x_408 = lean_nat_add(x_10, x_407);
lean_dec(x_10);
x_409 = l_Lean_Expr_mvarId_x21(x_405);
x_410 = lean_array_push(x_12, x_409);
lean_ctor_set(x_1, 5, x_410);
lean_ctor_set(x_1, 3, x_408);
lean_inc(x_405);
x_411 = l_Lean_mkApp(x_2, x_405);
x_412 = lean_expr_instantiate1(x_95, x_405);
lean_dec(x_405);
lean_dec(x_95);
x_2 = x_411;
x_3 = x_412;
x_5 = x_406;
goto _start;
}
else
{
lean_object* x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_1);
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_94);
x_415 = 1;
x_416 = lean_box(0);
lean_inc(x_4);
x_417 = l_Lean_Elab_Term_mkFreshExprMVar(x_414, x_415, x_416, x_4, x_49);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_unsigned_to_nat(1u);
x_421 = lean_nat_add(x_10, x_420);
lean_dec(x_10);
x_422 = l_Lean_Expr_mvarId_x21(x_418);
x_423 = lean_array_push(x_12, x_422);
x_424 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_424, 0, x_6);
lean_ctor_set(x_424, 1, x_7);
lean_ctor_set(x_424, 2, x_8);
lean_ctor_set(x_424, 3, x_421);
lean_ctor_set(x_424, 4, x_11);
lean_ctor_set(x_424, 5, x_423);
lean_ctor_set(x_424, 6, x_13);
lean_ctor_set_uint8(x_424, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_424, sizeof(void*)*7 + 1, x_15);
lean_inc(x_418);
x_425 = l_Lean_mkApp(x_2, x_418);
x_426 = lean_expr_instantiate1(x_95, x_418);
lean_dec(x_418);
lean_dec(x_95);
x_1 = x_424;
x_2 = x_425;
x_3 = x_426;
x_5 = x_419;
goto _start;
}
}
}
}
default: 
{
lean_object* x_428; uint8_t x_429; 
lean_dec(x_100);
lean_inc(x_4);
lean_inc(x_1);
x_428 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_48, x_4, x_49);
x_429 = !lean_is_exclusive(x_1);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_430 = lean_ctor_get(x_1, 6);
lean_dec(x_430);
x_431 = lean_ctor_get(x_1, 5);
lean_dec(x_431);
x_432 = lean_ctor_get(x_1, 4);
lean_dec(x_432);
x_433 = lean_ctor_get(x_1, 3);
lean_dec(x_433);
x_434 = lean_ctor_get(x_1, 2);
lean_dec(x_434);
x_435 = lean_ctor_get(x_1, 1);
lean_dec(x_435);
x_436 = lean_ctor_get(x_1, 0);
lean_dec(x_436);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_437; uint8_t x_438; lean_object* x_439; uint8_t x_440; 
x_437 = lean_ctor_get(x_428, 1);
lean_inc(x_437);
lean_dec(x_428);
x_438 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_438);
x_439 = lean_array_get_size(x_7);
x_440 = lean_nat_dec_lt(x_10, x_439);
lean_dec(x_439);
if (x_440 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_441; 
x_441 = l_Lean_Expr_getOptParamDefault_x3f(x_94);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; 
x_442 = l_Lean_Expr_getAutoParamTactic_x3f(x_94);
if (lean_obj_tag(x_442) == 0)
{
uint8_t x_443; 
lean_dec(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_443 = l_Array_isEmpty___rarg(x_11);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_444 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_444, 0, x_93);
x_445 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_446 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_444);
x_447 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_448 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
x_449 = x_11;
x_450 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_449);
x_451 = x_450;
x_452 = l_Array_toList___rarg(x_451);
lean_dec(x_451);
x_453 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_452);
x_454 = l_Array_HasRepr___rarg___closed__1;
x_455 = lean_string_append(x_454, x_453);
lean_dec(x_453);
x_456 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_456, 0, x_455);
x_457 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_457, 0, x_456);
x_458 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_458, 0, x_448);
lean_ctor_set(x_458, 1, x_457);
x_459 = l_Lean_Elab_Term_throwError___rarg(x_458, x_4, x_437);
return x_459;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; 
lean_dec(x_93);
lean_dec(x_11);
x_460 = l_Lean_Elab_Term_getOptions(x_4, x_437);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_463 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_464 = l_Lean_checkTraceOption(x_461, x_463);
lean_dec(x_461);
if (x_464 == 0)
{
x_18 = x_462;
goto block_46;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_inc(x_2);
x_465 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_465, 0, x_2);
x_466 = l_Lean_Elab_Term_logTrace(x_463, x_465, x_4, x_462);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_18 = x_467;
goto block_46;
}
}
}
else
{
lean_object* x_468; 
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_468 = lean_ctor_get(x_442, 0);
lean_inc(x_468);
lean_dec(x_442);
if (lean_obj_tag(x_468) == 4)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
lean_dec(x_468);
x_470 = l_Lean_Elab_Term_getEnv___rarg(x_437);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_471, x_469);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
lean_dec(x_473);
x_475 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_475, 0, x_474);
x_476 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_476, 0, x_475);
x_477 = l_Lean_Elab_Term_throwError___rarg(x_476, x_4, x_472);
return x_477;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_478 = lean_ctor_get(x_473, 0);
lean_inc(x_478);
lean_dec(x_473);
x_479 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_472);
x_480 = lean_ctor_get(x_479, 1);
lean_inc(x_480);
lean_dec(x_479);
x_481 = l_Lean_Elab_Term_getMainModule___rarg(x_480);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
lean_dec(x_481);
x_483 = l_Lean_Syntax_getArgs(x_478);
lean_dec(x_478);
x_484 = l_Array_empty___closed__1;
x_485 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_483, x_483, x_97, x_484);
lean_dec(x_483);
x_486 = l_Lean_nullKind___closed__2;
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_488 = lean_array_push(x_484, x_487);
x_489 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_488);
x_491 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_492 = lean_array_push(x_491, x_490);
x_493 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_494 = lean_array_push(x_492, x_493);
x_495 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_494);
x_497 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_498 = l_Lean_Expr_getAppNumArgsAux___main(x_94, x_97);
x_499 = lean_nat_sub(x_498, x_97);
lean_dec(x_498);
x_500 = lean_unsigned_to_nat(1u);
x_501 = lean_nat_sub(x_499, x_500);
lean_dec(x_499);
x_502 = l_Lean_Expr_getRevArg_x21___main(x_94, x_501);
lean_dec(x_94);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_503; lean_object* x_504; 
x_503 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_503, 0, x_496);
lean_inc(x_4);
lean_inc(x_2);
x_504 = l___private_Lean_Elab_App_2__elabArg(x_2, x_503, x_502, x_4, x_482);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
lean_inc(x_505);
x_507 = l_Lean_mkApp(x_2, x_505);
x_508 = lean_expr_instantiate1(x_95, x_505);
lean_dec(x_505);
lean_dec(x_95);
x_2 = x_507;
x_3 = x_508;
x_5 = x_506;
goto _start;
}
else
{
uint8_t x_510; 
lean_dec(x_1);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_510 = !lean_is_exclusive(x_504);
if (x_510 == 0)
{
return x_504;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_504, 0);
x_512 = lean_ctor_get(x_504, 1);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_504);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_514 = lean_ctor_get(x_497, 0);
lean_inc(x_514);
lean_dec(x_497);
x_515 = l_Lean_Syntax_replaceInfo___main(x_514, x_496);
x_516 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_516, 0, x_515);
lean_inc(x_4);
lean_inc(x_2);
x_517 = l___private_Lean_Elab_App_2__elabArg(x_2, x_516, x_502, x_4, x_482);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
lean_inc(x_518);
x_520 = l_Lean_mkApp(x_2, x_518);
x_521 = lean_expr_instantiate1(x_95, x_518);
lean_dec(x_518);
lean_dec(x_95);
x_2 = x_520;
x_3 = x_521;
x_5 = x_519;
goto _start;
}
else
{
uint8_t x_523; 
lean_dec(x_1);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_523 = !lean_is_exclusive(x_517);
if (x_523 == 0)
{
return x_517;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_517, 0);
x_525 = lean_ctor_get(x_517, 1);
lean_inc(x_525);
lean_inc(x_524);
lean_dec(x_517);
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
return x_526;
}
}
}
}
}
else
{
lean_object* x_527; lean_object* x_528; 
lean_dec(x_468);
lean_dec(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_527 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_528 = l_Lean_Elab_Term_throwError___rarg(x_527, x_4, x_437);
return x_528;
}
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_529 = lean_ctor_get(x_441, 0);
lean_inc(x_529);
lean_dec(x_441);
lean_inc(x_529);
x_530 = l_Lean_mkApp(x_2, x_529);
x_531 = lean_expr_instantiate1(x_95, x_529);
lean_dec(x_529);
lean_dec(x_95);
x_2 = x_530;
x_3 = x_531;
x_5 = x_437;
goto _start;
}
}
else
{
uint8_t x_533; 
lean_dec(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_533 = l_Array_isEmpty___rarg(x_11);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_534 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_534, 0, x_93);
x_535 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_536 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_534);
x_537 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_538 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
x_539 = x_11;
x_540 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_539);
x_541 = x_540;
x_542 = l_Array_toList___rarg(x_541);
lean_dec(x_541);
x_543 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_542);
x_544 = l_Array_HasRepr___rarg___closed__1;
x_545 = lean_string_append(x_544, x_543);
lean_dec(x_543);
x_546 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_546, 0, x_545);
x_547 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_547, 0, x_546);
x_548 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_548, 0, x_538);
lean_ctor_set(x_548, 1, x_547);
x_549 = l_Lean_Elab_Term_throwError___rarg(x_548, x_4, x_437);
return x_549;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; 
lean_dec(x_93);
lean_dec(x_11);
x_550 = l_Lean_Elab_Term_getOptions(x_4, x_437);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec(x_550);
x_553 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_554 = l_Lean_checkTraceOption(x_551, x_553);
lean_dec(x_551);
if (x_554 == 0)
{
x_18 = x_552;
goto block_46;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_inc(x_2);
x_555 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_555, 0, x_2);
x_556 = l_Lean_Elab_Term_logTrace(x_553, x_555, x_4, x_552);
x_557 = lean_ctor_get(x_556, 1);
lean_inc(x_557);
lean_dec(x_556);
x_18 = x_557;
goto block_46;
}
}
}
}
else
{
lean_object* x_558; lean_object* x_559; 
lean_dec(x_1);
lean_dec(x_93);
lean_dec(x_3);
x_558 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_559 = l___private_Lean_Elab_App_2__elabArg(x_2, x_558, x_94, x_4, x_437);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_unsigned_to_nat(1u);
x_563 = lean_nat_add(x_10, x_562);
lean_dec(x_10);
x_564 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_564, 0, x_6);
lean_ctor_set(x_564, 1, x_7);
lean_ctor_set(x_564, 2, x_8);
lean_ctor_set(x_564, 3, x_563);
lean_ctor_set(x_564, 4, x_11);
lean_ctor_set(x_564, 5, x_12);
lean_ctor_set(x_564, 6, x_13);
lean_ctor_set_uint8(x_564, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_564, sizeof(void*)*7 + 1, x_438);
lean_inc(x_560);
x_565 = l_Lean_mkApp(x_2, x_560);
x_566 = lean_expr_instantiate1(x_95, x_560);
lean_dec(x_560);
lean_dec(x_95);
x_1 = x_564;
x_2 = x_565;
x_3 = x_566;
x_5 = x_561;
goto _start;
}
else
{
uint8_t x_568; 
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_568 = !lean_is_exclusive(x_559);
if (x_568 == 0)
{
return x_559;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_559, 0);
x_570 = lean_ctor_get(x_559, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_559);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
return x_571;
}
}
}
}
else
{
uint8_t x_572; 
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_572 = !lean_is_exclusive(x_428);
if (x_572 == 0)
{
return x_428;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_ctor_get(x_428, 0);
x_574 = lean_ctor_get(x_428, 1);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_428);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_573);
lean_ctor_set(x_575, 1, x_574);
return x_575;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; 
x_576 = lean_ctor_get(x_428, 1);
lean_inc(x_576);
lean_dec(x_428);
x_577 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_578 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_578, 0, x_6);
lean_ctor_set(x_578, 1, x_7);
lean_ctor_set(x_578, 2, x_8);
lean_ctor_set(x_578, 3, x_10);
lean_ctor_set(x_578, 4, x_11);
lean_ctor_set(x_578, 5, x_12);
lean_ctor_set(x_578, 6, x_13);
lean_ctor_set_uint8(x_578, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_578, sizeof(void*)*7 + 1, x_577);
x_579 = lean_array_get_size(x_7);
x_580 = lean_nat_dec_lt(x_10, x_579);
lean_dec(x_579);
if (x_580 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_581; 
x_581 = l_Lean_Expr_getOptParamDefault_x3f(x_94);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; 
x_582 = l_Lean_Expr_getAutoParamTactic_x3f(x_94);
if (lean_obj_tag(x_582) == 0)
{
uint8_t x_583; 
lean_dec(x_578);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_583 = l_Array_isEmpty___rarg(x_11);
if (x_583 == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_584 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_584, 0, x_93);
x_585 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_586 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_584);
x_587 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_588 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_588, 0, x_586);
lean_ctor_set(x_588, 1, x_587);
x_589 = x_11;
x_590 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_589);
x_591 = x_590;
x_592 = l_Array_toList___rarg(x_591);
lean_dec(x_591);
x_593 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_592);
x_594 = l_Array_HasRepr___rarg___closed__1;
x_595 = lean_string_append(x_594, x_593);
lean_dec(x_593);
x_596 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_596, 0, x_595);
x_597 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_597, 0, x_596);
x_598 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_598, 0, x_588);
lean_ctor_set(x_598, 1, x_597);
x_599 = l_Lean_Elab_Term_throwError___rarg(x_598, x_4, x_576);
return x_599;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_93);
lean_dec(x_11);
x_600 = l_Lean_Elab_Term_getOptions(x_4, x_576);
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
x_603 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_604 = l_Lean_checkTraceOption(x_601, x_603);
lean_dec(x_601);
if (x_604 == 0)
{
x_18 = x_602;
goto block_46;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_inc(x_2);
x_605 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_605, 0, x_2);
x_606 = l_Lean_Elab_Term_logTrace(x_603, x_605, x_4, x_602);
x_607 = lean_ctor_get(x_606, 1);
lean_inc(x_607);
lean_dec(x_606);
x_18 = x_607;
goto block_46;
}
}
}
else
{
lean_object* x_608; 
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_608 = lean_ctor_get(x_582, 0);
lean_inc(x_608);
lean_dec(x_582);
if (lean_obj_tag(x_608) == 4)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
lean_dec(x_608);
x_610 = l_Lean_Elab_Term_getEnv___rarg(x_576);
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_610, 1);
lean_inc(x_612);
lean_dec(x_610);
x_613 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_611, x_609);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_578);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
lean_dec(x_613);
x_615 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_615, 0, x_614);
x_616 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_616, 0, x_615);
x_617 = l_Lean_Elab_Term_throwError___rarg(x_616, x_4, x_612);
return x_617;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_618 = lean_ctor_get(x_613, 0);
lean_inc(x_618);
lean_dec(x_613);
x_619 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_612);
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
lean_dec(x_619);
x_621 = l_Lean_Elab_Term_getMainModule___rarg(x_620);
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
lean_dec(x_621);
x_623 = l_Lean_Syntax_getArgs(x_618);
lean_dec(x_618);
x_624 = l_Array_empty___closed__1;
x_625 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_623, x_623, x_97, x_624);
lean_dec(x_623);
x_626 = l_Lean_nullKind___closed__2;
x_627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_625);
x_628 = lean_array_push(x_624, x_627);
x_629 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_628);
x_631 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_632 = lean_array_push(x_631, x_630);
x_633 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_634 = lean_array_push(x_632, x_633);
x_635 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_634);
x_637 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_638 = l_Lean_Expr_getAppNumArgsAux___main(x_94, x_97);
x_639 = lean_nat_sub(x_638, x_97);
lean_dec(x_638);
x_640 = lean_unsigned_to_nat(1u);
x_641 = lean_nat_sub(x_639, x_640);
lean_dec(x_639);
x_642 = l_Lean_Expr_getRevArg_x21___main(x_94, x_641);
lean_dec(x_94);
if (lean_obj_tag(x_637) == 0)
{
lean_object* x_643; lean_object* x_644; 
x_643 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_643, 0, x_636);
lean_inc(x_4);
lean_inc(x_2);
x_644 = l___private_Lean_Elab_App_2__elabArg(x_2, x_643, x_642, x_4, x_622);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec(x_644);
lean_inc(x_645);
x_647 = l_Lean_mkApp(x_2, x_645);
x_648 = lean_expr_instantiate1(x_95, x_645);
lean_dec(x_645);
lean_dec(x_95);
x_1 = x_578;
x_2 = x_647;
x_3 = x_648;
x_5 = x_646;
goto _start;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_578);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_650 = lean_ctor_get(x_644, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_644, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 lean_ctor_release(x_644, 1);
 x_652 = x_644;
} else {
 lean_dec_ref(x_644);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_650);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_654 = lean_ctor_get(x_637, 0);
lean_inc(x_654);
lean_dec(x_637);
x_655 = l_Lean_Syntax_replaceInfo___main(x_654, x_636);
x_656 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_656, 0, x_655);
lean_inc(x_4);
lean_inc(x_2);
x_657 = l___private_Lean_Elab_App_2__elabArg(x_2, x_656, x_642, x_4, x_622);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
lean_inc(x_658);
x_660 = l_Lean_mkApp(x_2, x_658);
x_661 = lean_expr_instantiate1(x_95, x_658);
lean_dec(x_658);
lean_dec(x_95);
x_1 = x_578;
x_2 = x_660;
x_3 = x_661;
x_5 = x_659;
goto _start;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_dec(x_578);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_663 = lean_ctor_get(x_657, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_657, 1);
lean_inc(x_664);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_665 = x_657;
} else {
 lean_dec_ref(x_657);
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
}
}
else
{
lean_object* x_667; lean_object* x_668; 
lean_dec(x_608);
lean_dec(x_578);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_667 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_668 = l_Lean_Elab_Term_throwError___rarg(x_667, x_4, x_576);
return x_668;
}
}
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_669 = lean_ctor_get(x_581, 0);
lean_inc(x_669);
lean_dec(x_581);
lean_inc(x_669);
x_670 = l_Lean_mkApp(x_2, x_669);
x_671 = lean_expr_instantiate1(x_95, x_669);
lean_dec(x_669);
lean_dec(x_95);
x_1 = x_578;
x_2 = x_670;
x_3 = x_671;
x_5 = x_576;
goto _start;
}
}
else
{
uint8_t x_673; 
lean_dec(x_578);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_673 = l_Array_isEmpty___rarg(x_11);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_674 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_674, 0, x_93);
x_675 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_676 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_674);
x_677 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_678 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
x_679 = x_11;
x_680 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_679);
x_681 = x_680;
x_682 = l_Array_toList___rarg(x_681);
lean_dec(x_681);
x_683 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_682);
x_684 = l_Array_HasRepr___rarg___closed__1;
x_685 = lean_string_append(x_684, x_683);
lean_dec(x_683);
x_686 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_686, 0, x_685);
x_687 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_687, 0, x_686);
x_688 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_688, 0, x_678);
lean_ctor_set(x_688, 1, x_687);
x_689 = l_Lean_Elab_Term_throwError___rarg(x_688, x_4, x_576);
return x_689;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; 
lean_dec(x_93);
lean_dec(x_11);
x_690 = l_Lean_Elab_Term_getOptions(x_4, x_576);
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
x_693 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_694 = l_Lean_checkTraceOption(x_691, x_693);
lean_dec(x_691);
if (x_694 == 0)
{
x_18 = x_692;
goto block_46;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_inc(x_2);
x_695 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_695, 0, x_2);
x_696 = l_Lean_Elab_Term_logTrace(x_693, x_695, x_4, x_692);
x_697 = lean_ctor_get(x_696, 1);
lean_inc(x_697);
lean_dec(x_696);
x_18 = x_697;
goto block_46;
}
}
}
}
else
{
lean_object* x_698; lean_object* x_699; 
lean_dec(x_578);
lean_dec(x_93);
lean_dec(x_3);
x_698 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_699 = l___private_Lean_Elab_App_2__elabArg(x_2, x_698, x_94, x_4, x_576);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = lean_unsigned_to_nat(1u);
x_703 = lean_nat_add(x_10, x_702);
lean_dec(x_10);
x_704 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_704, 0, x_6);
lean_ctor_set(x_704, 1, x_7);
lean_ctor_set(x_704, 2, x_8);
lean_ctor_set(x_704, 3, x_703);
lean_ctor_set(x_704, 4, x_11);
lean_ctor_set(x_704, 5, x_12);
lean_ctor_set(x_704, 6, x_13);
lean_ctor_set_uint8(x_704, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_704, sizeof(void*)*7 + 1, x_577);
lean_inc(x_700);
x_705 = l_Lean_mkApp(x_2, x_700);
x_706 = lean_expr_instantiate1(x_95, x_700);
lean_dec(x_700);
lean_dec(x_95);
x_1 = x_704;
x_2 = x_705;
x_3 = x_706;
x_5 = x_701;
goto _start;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_708 = lean_ctor_get(x_699, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_699, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_710 = x_699;
} else {
 lean_dec_ref(x_699);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_710)) {
 x_711 = lean_alloc_ctor(1, 2, 0);
} else {
 x_711 = x_710;
}
lean_ctor_set(x_711, 0, x_708);
lean_ctor_set(x_711, 1, x_709);
return x_711;
}
}
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_712 = lean_ctor_get(x_428, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_428, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_714 = x_428;
} else {
 lean_dec_ref(x_428);
 x_714 = lean_box(0);
}
if (lean_is_scalar(x_714)) {
 x_715 = lean_alloc_ctor(1, 2, 0);
} else {
 x_715 = x_714;
}
lean_ctor_set(x_715, 0, x_712);
lean_ctor_set(x_715, 1, x_713);
return x_715;
}
}
}
}
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_93);
lean_dec(x_3);
x_716 = lean_ctor_get(x_98, 0);
lean_inc(x_716);
lean_dec(x_98);
x_717 = l_Lean_Elab_Term_NamedArg_inhabited;
x_718 = lean_array_get(x_717, x_11, x_716);
x_719 = l_Array_eraseIdx___rarg(x_11, x_716);
lean_dec(x_716);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
lean_inc(x_4);
lean_inc(x_2);
x_721 = l___private_Lean_Elab_App_2__elabArg(x_2, x_720, x_94, x_4, x_49);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
lean_inc(x_4);
lean_inc(x_1);
x_724 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_48, x_4, x_723);
x_725 = !lean_is_exclusive(x_1);
if (x_725 == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_726 = lean_ctor_get(x_1, 6);
lean_dec(x_726);
x_727 = lean_ctor_get(x_1, 5);
lean_dec(x_727);
x_728 = lean_ctor_get(x_1, 4);
lean_dec(x_728);
x_729 = lean_ctor_get(x_1, 3);
lean_dec(x_729);
x_730 = lean_ctor_get(x_1, 2);
lean_dec(x_730);
x_731 = lean_ctor_get(x_1, 1);
lean_dec(x_731);
x_732 = lean_ctor_get(x_1, 0);
lean_dec(x_732);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_733; uint8_t x_734; lean_object* x_735; lean_object* x_736; 
x_733 = lean_ctor_get(x_724, 1);
lean_inc(x_733);
lean_dec(x_724);
x_734 = 1;
lean_ctor_set(x_1, 4, x_719);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_734);
lean_inc(x_722);
x_735 = l_Lean_mkApp(x_2, x_722);
x_736 = lean_expr_instantiate1(x_95, x_722);
lean_dec(x_722);
lean_dec(x_95);
x_2 = x_735;
x_3 = x_736;
x_5 = x_733;
goto _start;
}
else
{
uint8_t x_738; 
lean_free_object(x_1);
lean_dec(x_722);
lean_dec(x_719);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_738 = !lean_is_exclusive(x_724);
if (x_738 == 0)
{
return x_724;
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; 
x_739 = lean_ctor_get(x_724, 0);
x_740 = lean_ctor_get(x_724, 1);
lean_inc(x_740);
lean_inc(x_739);
lean_dec(x_724);
x_741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_741, 0, x_739);
lean_ctor_set(x_741, 1, x_740);
return x_741;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_742; uint8_t x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_742 = lean_ctor_get(x_724, 1);
lean_inc(x_742);
lean_dec(x_724);
x_743 = 1;
x_744 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_744, 0, x_6);
lean_ctor_set(x_744, 1, x_7);
lean_ctor_set(x_744, 2, x_8);
lean_ctor_set(x_744, 3, x_10);
lean_ctor_set(x_744, 4, x_719);
lean_ctor_set(x_744, 5, x_12);
lean_ctor_set(x_744, 6, x_13);
lean_ctor_set_uint8(x_744, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_744, sizeof(void*)*7 + 1, x_743);
lean_inc(x_722);
x_745 = l_Lean_mkApp(x_2, x_722);
x_746 = lean_expr_instantiate1(x_95, x_722);
lean_dec(x_722);
lean_dec(x_95);
x_1 = x_744;
x_2 = x_745;
x_3 = x_746;
x_5 = x_742;
goto _start;
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_722);
lean_dec(x_719);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_748 = lean_ctor_get(x_724, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_724, 1);
lean_inc(x_749);
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 lean_ctor_release(x_724, 1);
 x_750 = x_724;
} else {
 lean_dec_ref(x_724);
 x_750 = lean_box(0);
}
if (lean_is_scalar(x_750)) {
 x_751 = lean_alloc_ctor(1, 2, 0);
} else {
 x_751 = x_750;
}
lean_ctor_set(x_751, 0, x_748);
lean_ctor_set(x_751, 1, x_749);
return x_751;
}
}
}
else
{
uint8_t x_752; 
lean_dec(x_719);
lean_dec(x_95);
lean_dec(x_48);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_752 = !lean_is_exclusive(x_721);
if (x_752 == 0)
{
return x_721;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_721, 0);
x_754 = lean_ctor_get(x_721, 1);
lean_inc(x_754);
lean_inc(x_753);
lean_dec(x_721);
x_755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
return x_755;
}
}
}
}
else
{
lean_object* x_756; 
lean_dec(x_13);
lean_dec(x_6);
x_756 = lean_box(0);
x_50 = x_756;
goto block_92;
}
block_92:
{
uint8_t x_51; 
lean_dec(x_50);
x_51 = l_Array_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_inc(x_4);
x_52 = l___private_Lean_Elab_App_4__tryCoeFun(x_48, x_2, x_4, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_4);
lean_inc(x_53);
x_55 = l_Lean_Elab_Term_inferType(x_53, x_4, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_2 = x_53;
x_3 = x_56;
x_5 = x_57;
goto _start;
}
else
{
uint8_t x_59; 
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_4);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
return x_52;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_52, 0);
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_52);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_array_get_size(x_7);
lean_dec(x_7);
x_68 = lean_nat_dec_eq(x_10, x_67);
lean_dec(x_67);
lean_dec(x_10);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_inc(x_4);
x_69 = l___private_Lean_Elab_App_4__tryCoeFun(x_48, x_2, x_4, x_49);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_4);
lean_inc(x_70);
x_72 = l_Lean_Elab_Term_inferType(x_70, x_4, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_2 = x_70;
x_3 = x_73;
x_5 = x_74;
goto _start;
}
else
{
uint8_t x_76; 
lean_dec(x_70);
lean_dec(x_4);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_72);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_4);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_69);
if (x_80 == 0)
{
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_69, 0);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_69);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_48);
lean_dec(x_1);
x_84 = l_Lean_Elab_Term_getOptions(x_4, x_49);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_88 = l_Lean_checkTraceOption(x_85, x_87);
lean_dec(x_85);
if (x_88 == 0)
{
x_18 = x_86;
goto block_46;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_inc(x_2);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_2);
x_90 = l_Lean_Elab_Term_logTrace(x_87, x_89, x_4, x_86);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_18 = x_91;
goto block_46;
}
}
}
}
}
else
{
uint8_t x_757; 
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_757 = !lean_is_exclusive(x_47);
if (x_757 == 0)
{
return x_47;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_758 = lean_ctor_get(x_47, 0);
x_759 = lean_ctor_get(x_47, 1);
lean_inc(x_759);
lean_inc(x_758);
lean_dec(x_47);
x_760 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_760, 0, x_758);
lean_ctor_set(x_760, 1, x_759);
return x_760;
}
}
block_46:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_19, x_4, x_18);
lean_dec(x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
lean_inc(x_4);
x_30 = l_Lean_Elab_Term_isDefEq(x_29, x_3, x_4, x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_32, x_4, x_31);
lean_dec(x_12);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_2);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_12);
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
}
}
else
{
uint8_t x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; uint8_t x_772; uint8_t x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_804; 
x_761 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_762 = lean_ctor_get(x_4, 0);
x_763 = lean_ctor_get(x_4, 1);
x_764 = lean_ctor_get(x_4, 2);
x_765 = lean_ctor_get(x_4, 3);
x_766 = lean_ctor_get(x_4, 4);
x_767 = lean_ctor_get(x_4, 5);
x_768 = lean_ctor_get(x_4, 6);
x_769 = lean_ctor_get(x_4, 7);
x_770 = lean_ctor_get(x_4, 8);
x_771 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_772 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_773 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_774 = lean_ctor_get(x_4, 9);
lean_inc(x_774);
lean_inc(x_770);
lean_inc(x_769);
lean_inc(x_768);
lean_inc(x_767);
lean_inc(x_766);
lean_inc(x_765);
lean_inc(x_764);
lean_inc(x_763);
lean_inc(x_762);
lean_dec(x_4);
x_775 = l_Lean_Elab_replaceRef(x_6, x_774);
lean_dec(x_774);
x_776 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_776, 0, x_762);
lean_ctor_set(x_776, 1, x_763);
lean_ctor_set(x_776, 2, x_764);
lean_ctor_set(x_776, 3, x_765);
lean_ctor_set(x_776, 4, x_766);
lean_ctor_set(x_776, 5, x_767);
lean_ctor_set(x_776, 6, x_768);
lean_ctor_set(x_776, 7, x_769);
lean_ctor_set(x_776, 8, x_770);
lean_ctor_set(x_776, 9, x_775);
lean_ctor_set_uint8(x_776, sizeof(void*)*10, x_771);
lean_ctor_set_uint8(x_776, sizeof(void*)*10 + 1, x_772);
lean_ctor_set_uint8(x_776, sizeof(void*)*10 + 2, x_773);
lean_inc(x_776);
lean_inc(x_3);
x_804 = l_Lean_Elab_Term_whnfForall(x_3, x_776, x_5);
if (lean_obj_tag(x_804) == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = lean_ctor_get(x_804, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_804, 1);
lean_inc(x_806);
lean_dec(x_804);
if (lean_obj_tag(x_805) == 7)
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; uint64_t x_853; lean_object* x_854; lean_object* x_855; 
x_850 = lean_ctor_get(x_805, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_805, 1);
lean_inc(x_851);
x_852 = lean_ctor_get(x_805, 2);
lean_inc(x_852);
x_853 = lean_ctor_get_uint64(x_805, sizeof(void*)*3);
x_854 = lean_unsigned_to_nat(0u);
x_855 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_850, x_11, x_854);
if (lean_obj_tag(x_855) == 0)
{
uint8_t x_856; lean_object* x_857; 
x_856 = (uint8_t)((x_853 << 24) >> 61);
x_857 = lean_box(x_856);
switch (lean_obj_tag(x_857)) {
case 1:
{
if (x_9 == 0)
{
lean_object* x_858; lean_object* x_859; uint8_t x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_850);
lean_dec(x_805);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_858 = x_1;
} else {
 lean_dec_ref(x_1);
 x_858 = lean_box(0);
}
x_859 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_859, 0, x_851);
x_860 = 0;
x_861 = lean_box(0);
lean_inc(x_776);
x_862 = l_Lean_Elab_Term_mkFreshExprMVar(x_859, x_860, x_861, x_776, x_806);
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_862, 1);
lean_inc(x_864);
lean_dec(x_862);
lean_inc(x_776);
lean_inc(x_863);
x_865 = l_Lean_Elab_Term_isTypeFormer(x_863, x_776, x_864);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; uint8_t x_867; 
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_unbox(x_866);
lean_dec(x_866);
if (x_867 == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; 
x_868 = lean_ctor_get(x_865, 1);
lean_inc(x_868);
lean_dec(x_865);
if (lean_is_scalar(x_858)) {
 x_869 = lean_alloc_ctor(0, 7, 2);
} else {
 x_869 = x_858;
}
lean_ctor_set(x_869, 0, x_6);
lean_ctor_set(x_869, 1, x_7);
lean_ctor_set(x_869, 2, x_8);
lean_ctor_set(x_869, 3, x_10);
lean_ctor_set(x_869, 4, x_11);
lean_ctor_set(x_869, 5, x_12);
lean_ctor_set(x_869, 6, x_13);
lean_ctor_set_uint8(x_869, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_869, sizeof(void*)*7 + 1, x_761);
lean_inc(x_863);
x_870 = l_Lean_mkApp(x_2, x_863);
x_871 = lean_expr_instantiate1(x_852, x_863);
lean_dec(x_863);
lean_dec(x_852);
x_1 = x_869;
x_2 = x_870;
x_3 = x_871;
x_4 = x_776;
x_5 = x_868;
goto _start;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_873 = lean_ctor_get(x_865, 1);
lean_inc(x_873);
lean_dec(x_865);
x_874 = l_Lean_Expr_mvarId_x21(x_863);
x_875 = lean_array_push(x_13, x_874);
if (lean_is_scalar(x_858)) {
 x_876 = lean_alloc_ctor(0, 7, 2);
} else {
 x_876 = x_858;
}
lean_ctor_set(x_876, 0, x_6);
lean_ctor_set(x_876, 1, x_7);
lean_ctor_set(x_876, 2, x_8);
lean_ctor_set(x_876, 3, x_10);
lean_ctor_set(x_876, 4, x_11);
lean_ctor_set(x_876, 5, x_12);
lean_ctor_set(x_876, 6, x_875);
lean_ctor_set_uint8(x_876, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_876, sizeof(void*)*7 + 1, x_761);
lean_inc(x_863);
x_877 = l_Lean_mkApp(x_2, x_863);
x_878 = lean_expr_instantiate1(x_852, x_863);
lean_dec(x_863);
lean_dec(x_852);
x_1 = x_876;
x_2 = x_877;
x_3 = x_878;
x_4 = x_776;
x_5 = x_873;
goto _start;
}
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_863);
lean_dec(x_858);
lean_dec(x_852);
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_880 = lean_ctor_get(x_865, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_865, 1);
lean_inc(x_881);
if (lean_is_exclusive(x_865)) {
 lean_ctor_release(x_865, 0);
 lean_ctor_release(x_865, 1);
 x_882 = x_865;
} else {
 lean_dec_ref(x_865);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(1, 2, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_880);
lean_ctor_set(x_883, 1, x_881);
return x_883;
}
}
else
{
lean_object* x_884; lean_object* x_885; 
lean_inc(x_776);
lean_inc(x_1);
x_884 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_805, x_776, x_806);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_885 = x_1;
} else {
 lean_dec_ref(x_1);
 x_885 = lean_box(0);
}
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_886; lean_object* x_887; uint8_t x_888; 
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
x_887 = lean_array_get_size(x_7);
x_888 = lean_nat_dec_lt(x_10, x_887);
lean_dec(x_887);
if (x_888 == 0)
{
uint8_t x_889; 
lean_dec(x_885);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_889 = l_Array_isEmpty___rarg(x_11);
if (x_889 == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_890 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_890, 0, x_850);
x_891 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_892 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_892, 0, x_891);
lean_ctor_set(x_892, 1, x_890);
x_893 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_894 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_894, 0, x_892);
lean_ctor_set(x_894, 1, x_893);
x_895 = x_11;
x_896 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_854, x_895);
x_897 = x_896;
x_898 = l_Array_toList___rarg(x_897);
lean_dec(x_897);
x_899 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_898);
x_900 = l_Array_HasRepr___rarg___closed__1;
x_901 = lean_string_append(x_900, x_899);
lean_dec(x_899);
x_902 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_902, 0, x_901);
x_903 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_903, 0, x_902);
x_904 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_904, 0, x_894);
lean_ctor_set(x_904, 1, x_903);
x_905 = l_Lean_Elab_Term_throwError___rarg(x_904, x_776, x_886);
return x_905;
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; uint8_t x_910; 
lean_dec(x_850);
lean_dec(x_11);
x_906 = l_Lean_Elab_Term_getOptions(x_776, x_886);
x_907 = lean_ctor_get(x_906, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_906, 1);
lean_inc(x_908);
lean_dec(x_906);
x_909 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_910 = l_Lean_checkTraceOption(x_907, x_909);
lean_dec(x_907);
if (x_910 == 0)
{
x_777 = x_908;
goto block_803;
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_inc(x_2);
x_911 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_911, 0, x_2);
x_912 = l_Lean_Elab_Term_logTrace(x_909, x_911, x_776, x_908);
x_913 = lean_ctor_get(x_912, 1);
lean_inc(x_913);
lean_dec(x_912);
x_777 = x_913;
goto block_803;
}
}
}
else
{
lean_object* x_914; lean_object* x_915; 
lean_dec(x_850);
lean_dec(x_3);
x_914 = lean_array_fget(x_7, x_10);
lean_inc(x_776);
lean_inc(x_2);
x_915 = l___private_Lean_Elab_App_2__elabArg(x_2, x_914, x_851, x_776, x_886);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; uint8_t x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
x_918 = lean_unsigned_to_nat(1u);
x_919 = lean_nat_add(x_10, x_918);
lean_dec(x_10);
x_920 = 1;
if (lean_is_scalar(x_885)) {
 x_921 = lean_alloc_ctor(0, 7, 2);
} else {
 x_921 = x_885;
}
lean_ctor_set(x_921, 0, x_6);
lean_ctor_set(x_921, 1, x_7);
lean_ctor_set(x_921, 2, x_8);
lean_ctor_set(x_921, 3, x_919);
lean_ctor_set(x_921, 4, x_11);
lean_ctor_set(x_921, 5, x_12);
lean_ctor_set(x_921, 6, x_13);
lean_ctor_set_uint8(x_921, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_921, sizeof(void*)*7 + 1, x_920);
lean_inc(x_916);
x_922 = l_Lean_mkApp(x_2, x_916);
x_923 = lean_expr_instantiate1(x_852, x_916);
lean_dec(x_916);
lean_dec(x_852);
x_1 = x_921;
x_2 = x_922;
x_3 = x_923;
x_4 = x_776;
x_5 = x_917;
goto _start;
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_885);
lean_dec(x_852);
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_925 = lean_ctor_get(x_915, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_915, 1);
lean_inc(x_926);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_927 = x_915;
} else {
 lean_dec_ref(x_915);
 x_927 = lean_box(0);
}
if (lean_is_scalar(x_927)) {
 x_928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_928 = x_927;
}
lean_ctor_set(x_928, 0, x_925);
lean_ctor_set(x_928, 1, x_926);
return x_928;
}
}
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
lean_dec(x_885);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_929 = lean_ctor_get(x_884, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_884, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 x_931 = x_884;
} else {
 lean_dec_ref(x_884);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(1, 2, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_929);
lean_ctor_set(x_932, 1, x_930);
return x_932;
}
}
}
case 3:
{
if (x_9 == 0)
{
lean_object* x_933; lean_object* x_934; uint8_t x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
lean_dec(x_850);
lean_dec(x_805);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_933 = x_1;
} else {
 lean_dec_ref(x_1);
 x_933 = lean_box(0);
}
x_934 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_934, 0, x_851);
x_935 = 1;
x_936 = lean_box(0);
lean_inc(x_776);
x_937 = l_Lean_Elab_Term_mkFreshExprMVar(x_934, x_935, x_936, x_776, x_806);
x_938 = lean_ctor_get(x_937, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_937, 1);
lean_inc(x_939);
lean_dec(x_937);
x_940 = l_Lean_Expr_mvarId_x21(x_938);
x_941 = lean_array_push(x_12, x_940);
if (lean_is_scalar(x_933)) {
 x_942 = lean_alloc_ctor(0, 7, 2);
} else {
 x_942 = x_933;
}
lean_ctor_set(x_942, 0, x_6);
lean_ctor_set(x_942, 1, x_7);
lean_ctor_set(x_942, 2, x_8);
lean_ctor_set(x_942, 3, x_10);
lean_ctor_set(x_942, 4, x_11);
lean_ctor_set(x_942, 5, x_941);
lean_ctor_set(x_942, 6, x_13);
lean_ctor_set_uint8(x_942, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_942, sizeof(void*)*7 + 1, x_761);
lean_inc(x_938);
x_943 = l_Lean_mkApp(x_2, x_938);
x_944 = lean_expr_instantiate1(x_852, x_938);
lean_dec(x_938);
lean_dec(x_852);
x_1 = x_942;
x_2 = x_943;
x_3 = x_944;
x_4 = x_776;
x_5 = x_939;
goto _start;
}
else
{
uint8_t x_946; 
x_946 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_946 == 0)
{
lean_object* x_947; lean_object* x_948; 
lean_inc(x_776);
lean_inc(x_1);
x_947 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_805, x_776, x_806);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_948 = x_1;
} else {
 lean_dec_ref(x_1);
 x_948 = lean_box(0);
}
if (lean_obj_tag(x_947) == 0)
{
lean_object* x_949; lean_object* x_950; uint8_t x_951; 
x_949 = lean_ctor_get(x_947, 1);
lean_inc(x_949);
lean_dec(x_947);
x_950 = lean_array_get_size(x_7);
x_951 = lean_nat_dec_lt(x_10, x_950);
lean_dec(x_950);
if (x_951 == 0)
{
uint8_t x_952; 
lean_dec(x_948);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_952 = l_Array_isEmpty___rarg(x_11);
if (x_952 == 0)
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_953 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_953, 0, x_850);
x_954 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_955 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_955, 0, x_954);
lean_ctor_set(x_955, 1, x_953);
x_956 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_957 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_957, 0, x_955);
lean_ctor_set(x_957, 1, x_956);
x_958 = x_11;
x_959 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_854, x_958);
x_960 = x_959;
x_961 = l_Array_toList___rarg(x_960);
lean_dec(x_960);
x_962 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_961);
x_963 = l_Array_HasRepr___rarg___closed__1;
x_964 = lean_string_append(x_963, x_962);
lean_dec(x_962);
x_965 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_965, 0, x_964);
x_966 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_966, 0, x_965);
x_967 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_967, 0, x_957);
lean_ctor_set(x_967, 1, x_966);
x_968 = l_Lean_Elab_Term_throwError___rarg(x_967, x_776, x_949);
return x_968;
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; uint8_t x_973; 
lean_dec(x_850);
lean_dec(x_11);
x_969 = l_Lean_Elab_Term_getOptions(x_776, x_949);
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
lean_dec(x_969);
x_972 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_973 = l_Lean_checkTraceOption(x_970, x_972);
lean_dec(x_970);
if (x_973 == 0)
{
x_777 = x_971;
goto block_803;
}
else
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; 
lean_inc(x_2);
x_974 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_974, 0, x_2);
x_975 = l_Lean_Elab_Term_logTrace(x_972, x_974, x_776, x_971);
x_976 = lean_ctor_get(x_975, 1);
lean_inc(x_976);
lean_dec(x_975);
x_777 = x_976;
goto block_803;
}
}
}
else
{
lean_object* x_977; lean_object* x_978; 
lean_dec(x_850);
lean_dec(x_3);
x_977 = lean_array_fget(x_7, x_10);
lean_inc(x_776);
lean_inc(x_2);
x_978 = l___private_Lean_Elab_App_2__elabArg(x_2, x_977, x_851, x_776, x_949);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; uint8_t x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_979 = lean_ctor_get(x_978, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_978, 1);
lean_inc(x_980);
lean_dec(x_978);
x_981 = lean_unsigned_to_nat(1u);
x_982 = lean_nat_add(x_10, x_981);
lean_dec(x_10);
x_983 = 1;
if (lean_is_scalar(x_948)) {
 x_984 = lean_alloc_ctor(0, 7, 2);
} else {
 x_984 = x_948;
}
lean_ctor_set(x_984, 0, x_6);
lean_ctor_set(x_984, 1, x_7);
lean_ctor_set(x_984, 2, x_8);
lean_ctor_set(x_984, 3, x_982);
lean_ctor_set(x_984, 4, x_11);
lean_ctor_set(x_984, 5, x_12);
lean_ctor_set(x_984, 6, x_13);
lean_ctor_set_uint8(x_984, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_984, sizeof(void*)*7 + 1, x_983);
lean_inc(x_979);
x_985 = l_Lean_mkApp(x_2, x_979);
x_986 = lean_expr_instantiate1(x_852, x_979);
lean_dec(x_979);
lean_dec(x_852);
x_1 = x_984;
x_2 = x_985;
x_3 = x_986;
x_4 = x_776;
x_5 = x_980;
goto _start;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
lean_dec(x_948);
lean_dec(x_852);
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_988 = lean_ctor_get(x_978, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_978, 1);
lean_inc(x_989);
if (lean_is_exclusive(x_978)) {
 lean_ctor_release(x_978, 0);
 lean_ctor_release(x_978, 1);
 x_990 = x_978;
} else {
 lean_dec_ref(x_978);
 x_990 = lean_box(0);
}
if (lean_is_scalar(x_990)) {
 x_991 = lean_alloc_ctor(1, 2, 0);
} else {
 x_991 = x_990;
}
lean_ctor_set(x_991, 0, x_988);
lean_ctor_set(x_991, 1, x_989);
return x_991;
}
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
lean_dec(x_948);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_992 = lean_ctor_get(x_947, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_947, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 lean_ctor_release(x_947, 1);
 x_994 = x_947;
} else {
 lean_dec_ref(x_947);
 x_994 = lean_box(0);
}
if (lean_is_scalar(x_994)) {
 x_995 = lean_alloc_ctor(1, 2, 0);
} else {
 x_995 = x_994;
}
lean_ctor_set(x_995, 0, x_992);
lean_ctor_set(x_995, 1, x_993);
return x_995;
}
}
else
{
lean_object* x_996; lean_object* x_997; uint8_t x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
lean_dec(x_850);
lean_dec(x_805);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_996 = x_1;
} else {
 lean_dec_ref(x_1);
 x_996 = lean_box(0);
}
x_997 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_997, 0, x_851);
x_998 = 1;
x_999 = lean_box(0);
lean_inc(x_776);
x_1000 = l_Lean_Elab_Term_mkFreshExprMVar(x_997, x_998, x_999, x_776, x_806);
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_1000, 1);
lean_inc(x_1002);
lean_dec(x_1000);
x_1003 = lean_unsigned_to_nat(1u);
x_1004 = lean_nat_add(x_10, x_1003);
lean_dec(x_10);
x_1005 = l_Lean_Expr_mvarId_x21(x_1001);
x_1006 = lean_array_push(x_12, x_1005);
if (lean_is_scalar(x_996)) {
 x_1007 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1007 = x_996;
}
lean_ctor_set(x_1007, 0, x_6);
lean_ctor_set(x_1007, 1, x_7);
lean_ctor_set(x_1007, 2, x_8);
lean_ctor_set(x_1007, 3, x_1004);
lean_ctor_set(x_1007, 4, x_11);
lean_ctor_set(x_1007, 5, x_1006);
lean_ctor_set(x_1007, 6, x_13);
lean_ctor_set_uint8(x_1007, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1007, sizeof(void*)*7 + 1, x_761);
lean_inc(x_1001);
x_1008 = l_Lean_mkApp(x_2, x_1001);
x_1009 = lean_expr_instantiate1(x_852, x_1001);
lean_dec(x_1001);
lean_dec(x_852);
x_1 = x_1007;
x_2 = x_1008;
x_3 = x_1009;
x_4 = x_776;
x_5 = x_1002;
goto _start;
}
}
}
default: 
{
lean_object* x_1011; lean_object* x_1012; 
lean_dec(x_857);
lean_inc(x_776);
lean_inc(x_1);
x_1011 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_805, x_776, x_806);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1012 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1012 = lean_box(0);
}
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1013; uint8_t x_1014; lean_object* x_1015; lean_object* x_1016; uint8_t x_1017; 
x_1013 = lean_ctor_get(x_1011, 1);
lean_inc(x_1013);
lean_dec(x_1011);
x_1014 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
if (lean_is_scalar(x_1012)) {
 x_1015 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1015 = x_1012;
}
lean_ctor_set(x_1015, 0, x_6);
lean_ctor_set(x_1015, 1, x_7);
lean_ctor_set(x_1015, 2, x_8);
lean_ctor_set(x_1015, 3, x_10);
lean_ctor_set(x_1015, 4, x_11);
lean_ctor_set(x_1015, 5, x_12);
lean_ctor_set(x_1015, 6, x_13);
lean_ctor_set_uint8(x_1015, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1015, sizeof(void*)*7 + 1, x_1014);
x_1016 = lean_array_get_size(x_7);
x_1017 = lean_nat_dec_lt(x_10, x_1016);
lean_dec(x_1016);
if (x_1017 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1018; 
x_1018 = l_Lean_Expr_getOptParamDefault_x3f(x_851);
if (lean_obj_tag(x_1018) == 0)
{
lean_object* x_1019; 
x_1019 = l_Lean_Expr_getAutoParamTactic_x3f(x_851);
if (lean_obj_tag(x_1019) == 0)
{
uint8_t x_1020; 
lean_dec(x_1015);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_6);
x_1020 = l_Array_isEmpty___rarg(x_11);
if (x_1020 == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1021 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1021, 0, x_850);
x_1022 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1023 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1021);
x_1024 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1025 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
x_1026 = x_11;
x_1027 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_854, x_1026);
x_1028 = x_1027;
x_1029 = l_Array_toList___rarg(x_1028);
lean_dec(x_1028);
x_1030 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1029);
x_1031 = l_Array_HasRepr___rarg___closed__1;
x_1032 = lean_string_append(x_1031, x_1030);
lean_dec(x_1030);
x_1033 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1033, 0, x_1032);
x_1034 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1034, 0, x_1033);
x_1035 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1035, 0, x_1025);
lean_ctor_set(x_1035, 1, x_1034);
x_1036 = l_Lean_Elab_Term_throwError___rarg(x_1035, x_776, x_1013);
return x_1036;
}
else
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; uint8_t x_1041; 
lean_dec(x_850);
lean_dec(x_11);
x_1037 = l_Lean_Elab_Term_getOptions(x_776, x_1013);
x_1038 = lean_ctor_get(x_1037, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
lean_dec(x_1037);
x_1040 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1041 = l_Lean_checkTraceOption(x_1038, x_1040);
lean_dec(x_1038);
if (x_1041 == 0)
{
x_777 = x_1039;
goto block_803;
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
lean_inc(x_2);
x_1042 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1042, 0, x_2);
x_1043 = l_Lean_Elab_Term_logTrace(x_1040, x_1042, x_776, x_1039);
x_1044 = lean_ctor_get(x_1043, 1);
lean_inc(x_1044);
lean_dec(x_1043);
x_777 = x_1044;
goto block_803;
}
}
}
else
{
lean_object* x_1045; 
lean_dec(x_850);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1045 = lean_ctor_get(x_1019, 0);
lean_inc(x_1045);
lean_dec(x_1019);
if (lean_obj_tag(x_1045) == 4)
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
lean_dec(x_1045);
x_1047 = l_Lean_Elab_Term_getEnv___rarg(x_1013);
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1047, 1);
lean_inc(x_1049);
lean_dec(x_1047);
x_1050 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1048, x_1046);
if (lean_obj_tag(x_1050) == 0)
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_1015);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_6);
lean_dec(x_2);
x_1051 = lean_ctor_get(x_1050, 0);
lean_inc(x_1051);
lean_dec(x_1050);
x_1052 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1052, 0, x_1051);
x_1053 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1053, 0, x_1052);
x_1054 = l_Lean_Elab_Term_throwError___rarg(x_1053, x_776, x_1049);
return x_1054;
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1055 = lean_ctor_get(x_1050, 0);
lean_inc(x_1055);
lean_dec(x_1050);
x_1056 = l_Lean_Elab_Term_getCurrMacroScope(x_776, x_1049);
x_1057 = lean_ctor_get(x_1056, 1);
lean_inc(x_1057);
lean_dec(x_1056);
x_1058 = l_Lean_Elab_Term_getMainModule___rarg(x_1057);
x_1059 = lean_ctor_get(x_1058, 1);
lean_inc(x_1059);
lean_dec(x_1058);
x_1060 = l_Lean_Syntax_getArgs(x_1055);
lean_dec(x_1055);
x_1061 = l_Array_empty___closed__1;
x_1062 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1060, x_1060, x_854, x_1061);
lean_dec(x_1060);
x_1063 = l_Lean_nullKind___closed__2;
x_1064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1064, 0, x_1063);
lean_ctor_set(x_1064, 1, x_1062);
x_1065 = lean_array_push(x_1061, x_1064);
x_1066 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
x_1067 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1067, 0, x_1066);
lean_ctor_set(x_1067, 1, x_1065);
x_1068 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1069 = lean_array_push(x_1068, x_1067);
x_1070 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1071 = lean_array_push(x_1069, x_1070);
x_1072 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1073 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1073, 0, x_1072);
lean_ctor_set(x_1073, 1, x_1071);
x_1074 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_1075 = l_Lean_Expr_getAppNumArgsAux___main(x_851, x_854);
x_1076 = lean_nat_sub(x_1075, x_854);
lean_dec(x_1075);
x_1077 = lean_unsigned_to_nat(1u);
x_1078 = lean_nat_sub(x_1076, x_1077);
lean_dec(x_1076);
x_1079 = l_Lean_Expr_getRevArg_x21___main(x_851, x_1078);
lean_dec(x_851);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1080; lean_object* x_1081; 
x_1080 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1080, 0, x_1073);
lean_inc(x_776);
lean_inc(x_2);
x_1081 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1080, x_1079, x_776, x_1059);
if (lean_obj_tag(x_1081) == 0)
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
x_1082 = lean_ctor_get(x_1081, 0);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1081, 1);
lean_inc(x_1083);
lean_dec(x_1081);
lean_inc(x_1082);
x_1084 = l_Lean_mkApp(x_2, x_1082);
x_1085 = lean_expr_instantiate1(x_852, x_1082);
lean_dec(x_1082);
lean_dec(x_852);
x_1 = x_1015;
x_2 = x_1084;
x_3 = x_1085;
x_4 = x_776;
x_5 = x_1083;
goto _start;
}
else
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
lean_dec(x_1015);
lean_dec(x_852);
lean_dec(x_776);
lean_dec(x_2);
x_1087 = lean_ctor_get(x_1081, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1081, 1);
lean_inc(x_1088);
if (lean_is_exclusive(x_1081)) {
 lean_ctor_release(x_1081, 0);
 lean_ctor_release(x_1081, 1);
 x_1089 = x_1081;
} else {
 lean_dec_ref(x_1081);
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
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
x_1091 = lean_ctor_get(x_1074, 0);
lean_inc(x_1091);
lean_dec(x_1074);
x_1092 = l_Lean_Syntax_replaceInfo___main(x_1091, x_1073);
x_1093 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1093, 0, x_1092);
lean_inc(x_776);
lean_inc(x_2);
x_1094 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1093, x_1079, x_776, x_1059);
if (lean_obj_tag(x_1094) == 0)
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1095 = lean_ctor_get(x_1094, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1094, 1);
lean_inc(x_1096);
lean_dec(x_1094);
lean_inc(x_1095);
x_1097 = l_Lean_mkApp(x_2, x_1095);
x_1098 = lean_expr_instantiate1(x_852, x_1095);
lean_dec(x_1095);
lean_dec(x_852);
x_1 = x_1015;
x_2 = x_1097;
x_3 = x_1098;
x_4 = x_776;
x_5 = x_1096;
goto _start;
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_1015);
lean_dec(x_852);
lean_dec(x_776);
lean_dec(x_2);
x_1100 = lean_ctor_get(x_1094, 0);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1094, 1);
lean_inc(x_1101);
if (lean_is_exclusive(x_1094)) {
 lean_ctor_release(x_1094, 0);
 lean_ctor_release(x_1094, 1);
 x_1102 = x_1094;
} else {
 lean_dec_ref(x_1094);
 x_1102 = lean_box(0);
}
if (lean_is_scalar(x_1102)) {
 x_1103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1103 = x_1102;
}
lean_ctor_set(x_1103, 0, x_1100);
lean_ctor_set(x_1103, 1, x_1101);
return x_1103;
}
}
}
}
else
{
lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_1045);
lean_dec(x_1015);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_6);
lean_dec(x_2);
x_1104 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1105 = l_Lean_Elab_Term_throwError___rarg(x_1104, x_776, x_1013);
return x_1105;
}
}
}
else
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1106 = lean_ctor_get(x_1018, 0);
lean_inc(x_1106);
lean_dec(x_1018);
lean_inc(x_1106);
x_1107 = l_Lean_mkApp(x_2, x_1106);
x_1108 = lean_expr_instantiate1(x_852, x_1106);
lean_dec(x_1106);
lean_dec(x_852);
x_1 = x_1015;
x_2 = x_1107;
x_3 = x_1108;
x_4 = x_776;
x_5 = x_1013;
goto _start;
}
}
else
{
uint8_t x_1110; 
lean_dec(x_1015);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_6);
x_1110 = l_Array_isEmpty___rarg(x_11);
if (x_1110 == 0)
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1111 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1111, 0, x_850);
x_1112 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1113 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1113, 0, x_1112);
lean_ctor_set(x_1113, 1, x_1111);
x_1114 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1115, 0, x_1113);
lean_ctor_set(x_1115, 1, x_1114);
x_1116 = x_11;
x_1117 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_854, x_1116);
x_1118 = x_1117;
x_1119 = l_Array_toList___rarg(x_1118);
lean_dec(x_1118);
x_1120 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1119);
x_1121 = l_Array_HasRepr___rarg___closed__1;
x_1122 = lean_string_append(x_1121, x_1120);
lean_dec(x_1120);
x_1123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1123, 0, x_1122);
x_1124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1124, 0, x_1123);
x_1125 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1125, 0, x_1115);
lean_ctor_set(x_1125, 1, x_1124);
x_1126 = l_Lean_Elab_Term_throwError___rarg(x_1125, x_776, x_1013);
return x_1126;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; uint8_t x_1131; 
lean_dec(x_850);
lean_dec(x_11);
x_1127 = l_Lean_Elab_Term_getOptions(x_776, x_1013);
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1127, 1);
lean_inc(x_1129);
lean_dec(x_1127);
x_1130 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1131 = l_Lean_checkTraceOption(x_1128, x_1130);
lean_dec(x_1128);
if (x_1131 == 0)
{
x_777 = x_1129;
goto block_803;
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
lean_inc(x_2);
x_1132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1132, 0, x_2);
x_1133 = l_Lean_Elab_Term_logTrace(x_1130, x_1132, x_776, x_1129);
x_1134 = lean_ctor_get(x_1133, 1);
lean_inc(x_1134);
lean_dec(x_1133);
x_777 = x_1134;
goto block_803;
}
}
}
}
else
{
lean_object* x_1135; lean_object* x_1136; 
lean_dec(x_1015);
lean_dec(x_850);
lean_dec(x_3);
x_1135 = lean_array_fget(x_7, x_10);
lean_inc(x_776);
lean_inc(x_2);
x_1136 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1135, x_851, x_776, x_1013);
if (lean_obj_tag(x_1136) == 0)
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1137 = lean_ctor_get(x_1136, 0);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1136, 1);
lean_inc(x_1138);
lean_dec(x_1136);
x_1139 = lean_unsigned_to_nat(1u);
x_1140 = lean_nat_add(x_10, x_1139);
lean_dec(x_10);
x_1141 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1141, 0, x_6);
lean_ctor_set(x_1141, 1, x_7);
lean_ctor_set(x_1141, 2, x_8);
lean_ctor_set(x_1141, 3, x_1140);
lean_ctor_set(x_1141, 4, x_11);
lean_ctor_set(x_1141, 5, x_12);
lean_ctor_set(x_1141, 6, x_13);
lean_ctor_set_uint8(x_1141, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1141, sizeof(void*)*7 + 1, x_1014);
lean_inc(x_1137);
x_1142 = l_Lean_mkApp(x_2, x_1137);
x_1143 = lean_expr_instantiate1(x_852, x_1137);
lean_dec(x_1137);
lean_dec(x_852);
x_1 = x_1141;
x_2 = x_1142;
x_3 = x_1143;
x_4 = x_776;
x_5 = x_1138;
goto _start;
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
lean_dec(x_852);
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1145 = lean_ctor_get(x_1136, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1136, 1);
lean_inc(x_1146);
if (lean_is_exclusive(x_1136)) {
 lean_ctor_release(x_1136, 0);
 lean_ctor_release(x_1136, 1);
 x_1147 = x_1136;
} else {
 lean_dec_ref(x_1136);
 x_1147 = lean_box(0);
}
if (lean_is_scalar(x_1147)) {
 x_1148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1148 = x_1147;
}
lean_ctor_set(x_1148, 0, x_1145);
lean_ctor_set(x_1148, 1, x_1146);
return x_1148;
}
}
}
else
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
lean_dec(x_1012);
lean_dec(x_852);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_1149 = lean_ctor_get(x_1011, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1011, 1);
lean_inc(x_1150);
if (lean_is_exclusive(x_1011)) {
 lean_ctor_release(x_1011, 0);
 lean_ctor_release(x_1011, 1);
 x_1151 = x_1011;
} else {
 lean_dec_ref(x_1011);
 x_1151 = lean_box(0);
}
if (lean_is_scalar(x_1151)) {
 x_1152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1152 = x_1151;
}
lean_ctor_set(x_1152, 0, x_1149);
lean_ctor_set(x_1152, 1, x_1150);
return x_1152;
}
}
}
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_850);
lean_dec(x_3);
x_1153 = lean_ctor_get(x_855, 0);
lean_inc(x_1153);
lean_dec(x_855);
x_1154 = l_Lean_Elab_Term_NamedArg_inhabited;
x_1155 = lean_array_get(x_1154, x_11, x_1153);
x_1156 = l_Array_eraseIdx___rarg(x_11, x_1153);
lean_dec(x_1153);
x_1157 = lean_ctor_get(x_1155, 1);
lean_inc(x_1157);
lean_dec(x_1155);
lean_inc(x_776);
lean_inc(x_2);
x_1158 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1157, x_851, x_776, x_806);
if (lean_obj_tag(x_1158) == 0)
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1158, 1);
lean_inc(x_1160);
lean_dec(x_1158);
lean_inc(x_776);
lean_inc(x_1);
x_1161 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_805, x_776, x_1160);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1162 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1162 = lean_box(0);
}
if (lean_obj_tag(x_1161) == 0)
{
lean_object* x_1163; uint8_t x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1163 = lean_ctor_get(x_1161, 1);
lean_inc(x_1163);
lean_dec(x_1161);
x_1164 = 1;
if (lean_is_scalar(x_1162)) {
 x_1165 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1165 = x_1162;
}
lean_ctor_set(x_1165, 0, x_6);
lean_ctor_set(x_1165, 1, x_7);
lean_ctor_set(x_1165, 2, x_8);
lean_ctor_set(x_1165, 3, x_10);
lean_ctor_set(x_1165, 4, x_1156);
lean_ctor_set(x_1165, 5, x_12);
lean_ctor_set(x_1165, 6, x_13);
lean_ctor_set_uint8(x_1165, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1165, sizeof(void*)*7 + 1, x_1164);
lean_inc(x_1159);
x_1166 = l_Lean_mkApp(x_2, x_1159);
x_1167 = lean_expr_instantiate1(x_852, x_1159);
lean_dec(x_1159);
lean_dec(x_852);
x_1 = x_1165;
x_2 = x_1166;
x_3 = x_1167;
x_4 = x_776;
x_5 = x_1163;
goto _start;
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
lean_dec(x_1162);
lean_dec(x_1159);
lean_dec(x_1156);
lean_dec(x_852);
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1169 = lean_ctor_get(x_1161, 0);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1161, 1);
lean_inc(x_1170);
if (lean_is_exclusive(x_1161)) {
 lean_ctor_release(x_1161, 0);
 lean_ctor_release(x_1161, 1);
 x_1171 = x_1161;
} else {
 lean_dec_ref(x_1161);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_1169);
lean_ctor_set(x_1172, 1, x_1170);
return x_1172;
}
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
lean_dec(x_1156);
lean_dec(x_852);
lean_dec(x_805);
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_1173 = lean_ctor_get(x_1158, 0);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_1158, 1);
lean_inc(x_1174);
if (lean_is_exclusive(x_1158)) {
 lean_ctor_release(x_1158, 0);
 lean_ctor_release(x_1158, 1);
 x_1175 = x_1158;
} else {
 lean_dec_ref(x_1158);
 x_1175 = lean_box(0);
}
if (lean_is_scalar(x_1175)) {
 x_1176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1176 = x_1175;
}
lean_ctor_set(x_1176, 0, x_1173);
lean_ctor_set(x_1176, 1, x_1174);
return x_1176;
}
}
}
else
{
lean_object* x_1177; 
lean_dec(x_13);
lean_dec(x_6);
x_1177 = lean_box(0);
x_807 = x_1177;
goto block_849;
}
block_849:
{
uint8_t x_808; 
lean_dec(x_807);
x_808 = l_Array_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_808 == 0)
{
lean_object* x_809; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_inc(x_776);
x_809 = l___private_Lean_Elab_App_4__tryCoeFun(x_805, x_2, x_776, x_806);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_809, 1);
lean_inc(x_811);
lean_dec(x_809);
lean_inc(x_776);
lean_inc(x_810);
x_812 = l_Lean_Elab_Term_inferType(x_810, x_776, x_811);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; lean_object* x_814; 
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_812, 1);
lean_inc(x_814);
lean_dec(x_812);
x_2 = x_810;
x_3 = x_813;
x_4 = x_776;
x_5 = x_814;
goto _start;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
lean_dec(x_810);
lean_dec(x_776);
lean_dec(x_1);
x_816 = lean_ctor_get(x_812, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_812, 1);
lean_inc(x_817);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_818 = x_812;
} else {
 lean_dec_ref(x_812);
 x_818 = lean_box(0);
}
if (lean_is_scalar(x_818)) {
 x_819 = lean_alloc_ctor(1, 2, 0);
} else {
 x_819 = x_818;
}
lean_ctor_set(x_819, 0, x_816);
lean_ctor_set(x_819, 1, x_817);
return x_819;
}
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_776);
lean_dec(x_1);
x_820 = lean_ctor_get(x_809, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_809, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 x_822 = x_809;
} else {
 lean_dec_ref(x_809);
 x_822 = lean_box(0);
}
if (lean_is_scalar(x_822)) {
 x_823 = lean_alloc_ctor(1, 2, 0);
} else {
 x_823 = x_822;
}
lean_ctor_set(x_823, 0, x_820);
lean_ctor_set(x_823, 1, x_821);
return x_823;
}
}
else
{
lean_object* x_824; uint8_t x_825; 
x_824 = lean_array_get_size(x_7);
lean_dec(x_7);
x_825 = lean_nat_dec_eq(x_10, x_824);
lean_dec(x_824);
lean_dec(x_10);
if (x_825 == 0)
{
lean_object* x_826; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_inc(x_776);
x_826 = l___private_Lean_Elab_App_4__tryCoeFun(x_805, x_2, x_776, x_806);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
lean_inc(x_776);
lean_inc(x_827);
x_829 = l_Lean_Elab_Term_inferType(x_827, x_776, x_828);
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_830; lean_object* x_831; 
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec(x_829);
x_2 = x_827;
x_3 = x_830;
x_4 = x_776;
x_5 = x_831;
goto _start;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_dec(x_827);
lean_dec(x_776);
lean_dec(x_1);
x_833 = lean_ctor_get(x_829, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_829, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_835 = x_829;
} else {
 lean_dec_ref(x_829);
 x_835 = lean_box(0);
}
if (lean_is_scalar(x_835)) {
 x_836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_836 = x_835;
}
lean_ctor_set(x_836, 0, x_833);
lean_ctor_set(x_836, 1, x_834);
return x_836;
}
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; 
lean_dec(x_776);
lean_dec(x_1);
x_837 = lean_ctor_get(x_826, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_826, 1);
lean_inc(x_838);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_839 = x_826;
} else {
 lean_dec_ref(x_826);
 x_839 = lean_box(0);
}
if (lean_is_scalar(x_839)) {
 x_840 = lean_alloc_ctor(1, 2, 0);
} else {
 x_840 = x_839;
}
lean_ctor_set(x_840, 0, x_837);
lean_ctor_set(x_840, 1, x_838);
return x_840;
}
}
else
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; uint8_t x_845; 
lean_dec(x_805);
lean_dec(x_1);
x_841 = l_Lean_Elab_Term_getOptions(x_776, x_806);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
lean_dec(x_841);
x_844 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_845 = l_Lean_checkTraceOption(x_842, x_844);
lean_dec(x_842);
if (x_845 == 0)
{
x_777 = x_843;
goto block_803;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_inc(x_2);
x_846 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_846, 0, x_2);
x_847 = l_Lean_Elab_Term_logTrace(x_844, x_846, x_776, x_843);
x_848 = lean_ctor_get(x_847, 1);
lean_inc(x_848);
lean_dec(x_847);
x_777 = x_848;
goto block_803;
}
}
}
}
}
else
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_776);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1178 = lean_ctor_get(x_804, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_804, 1);
lean_inc(x_1179);
if (lean_is_exclusive(x_804)) {
 lean_ctor_release(x_804, 0);
 lean_ctor_release(x_804, 1);
 x_1180 = x_804;
} else {
 lean_dec_ref(x_804);
 x_1180 = lean_box(0);
}
if (lean_is_scalar(x_1180)) {
 x_1181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1181 = x_1180;
}
lean_ctor_set(x_1181, 0, x_1178);
lean_ctor_set(x_1181, 1, x_1179);
return x_1181;
}
block_803:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_778; lean_object* x_779; 
lean_dec(x_3);
x_778 = lean_unsigned_to_nat(0u);
x_779 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_778, x_776, x_777);
lean_dec(x_12);
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_780 = lean_ctor_get(x_779, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_779)) {
 lean_ctor_release(x_779, 0);
 lean_ctor_release(x_779, 1);
 x_781 = x_779;
} else {
 lean_dec_ref(x_779);
 x_781 = lean_box(0);
}
if (lean_is_scalar(x_781)) {
 x_782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_782 = x_781;
}
lean_ctor_set(x_782, 0, x_2);
lean_ctor_set(x_782, 1, x_780);
return x_782;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_2);
x_783 = lean_ctor_get(x_779, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_779, 1);
lean_inc(x_784);
if (lean_is_exclusive(x_779)) {
 lean_ctor_release(x_779, 0);
 lean_ctor_release(x_779, 1);
 x_785 = x_779;
} else {
 lean_dec_ref(x_779);
 x_785 = lean_box(0);
}
if (lean_is_scalar(x_785)) {
 x_786 = lean_alloc_ctor(1, 2, 0);
} else {
 x_786 = x_785;
}
lean_ctor_set(x_786, 0, x_783);
lean_ctor_set(x_786, 1, x_784);
return x_786;
}
}
else
{
lean_object* x_787; lean_object* x_788; 
x_787 = lean_ctor_get(x_8, 0);
lean_inc(x_787);
lean_dec(x_8);
lean_inc(x_776);
x_788 = l_Lean_Elab_Term_isDefEq(x_787, x_3, x_776, x_777);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_789 = lean_ctor_get(x_788, 1);
lean_inc(x_789);
lean_dec(x_788);
x_790 = lean_unsigned_to_nat(0u);
x_791 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_790, x_776, x_789);
lean_dec(x_12);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_791, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_793 = x_791;
} else {
 lean_dec_ref(x_791);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_2);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_2);
x_795 = lean_ctor_get(x_791, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_791, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_797 = x_791;
} else {
 lean_dec_ref(x_791);
 x_797 = lean_box(0);
}
if (lean_is_scalar(x_797)) {
 x_798 = lean_alloc_ctor(1, 2, 0);
} else {
 x_798 = x_797;
}
lean_ctor_set(x_798, 0, x_795);
lean_ctor_set(x_798, 1, x_796);
return x_798;
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_776);
lean_dec(x_12);
lean_dec(x_2);
x_799 = lean_ctor_get(x_788, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_788, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_801 = x_788;
} else {
 lean_dec_ref(x_788);
 x_801 = lean_box(0);
}
if (lean_is_scalar(x_801)) {
 x_802 = lean_alloc_ctor(1, 2, 0);
} else {
 x_802 = x_801;
}
lean_ctor_set(x_802, 0, x_799);
lean_ctor_set(x_802, 1, x_800);
return x_802;
}
}
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
lean_object* l___private_Lean_Elab_App_11__elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_Lean_Elab_Term_inferType(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
x_11 = l_Lean_Elab_Term_instantiateMVars(x_9, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_48 = l_Lean_Elab_Term_getOptions(x_6, x_13);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l___private_Lean_Elab_App_11__elabAppArgs___closed__2;
x_52 = l_Lean_checkTraceOption(x_49, x_51);
lean_dec(x_49);
if (x_52 == 0)
{
x_14 = x_50;
goto block_47;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_inc(x_1);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_1);
lean_inc(x_12);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_12);
if (x_5 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = l___private_Lean_Elab_App_11__elabAppArgs___closed__8;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
x_57 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_58 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
x_60 = l_Lean_Elab_Term_logTrace(x_51, x_59, x_6, x_50);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_14 = x_61;
goto block_47;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = l___private_Lean_Elab_App_11__elabAppArgs___closed__11;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_53);
x_64 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
x_67 = l_Lean_Elab_Term_logTrace(x_51, x_66, x_6, x_50);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_14 = x_68;
goto block_47;
}
}
block_47:
{
uint8_t x_15; 
x_15 = l_Array_isEmpty___rarg(x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc(x_6);
lean_inc(x_12);
x_16 = l_Lean_Elab_Term_tryPostponeIfMVar(x_12, x_6, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_6, 9);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_empty___closed__1;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_2);
lean_ctor_set(x_22, 5, x_20);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*7, x_5);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 1, x_21);
x_23 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_22, x_1, x_12, x_6, x_17);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_28; 
x_28 = l_Array_isEmpty___rarg(x_3);
if (x_28 == 0)
{
lean_object* x_29; 
lean_inc(x_6);
lean_inc(x_12);
x_29 = l_Lean_Elab_Term_tryPostponeIfMVar(x_12, x_6, x_14);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_6, 9);
lean_inc(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_empty___closed__1;
x_34 = 0;
x_35 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_2);
lean_ctor_set(x_35, 5, x_33);
lean_ctor_set(x_35, 6, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*7, x_5);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 1, x_34);
x_36 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_35, x_1, x_12, x_6, x_30);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_6, 9);
lean_inc(x_41);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_empty___closed__1;
x_44 = 0;
x_45 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set(x_45, 2, x_4);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_2);
lean_ctor_set(x_45, 5, x_43);
lean_ctor_set(x_45, 6, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*7, x_5);
lean_ctor_set_uint8(x_45, sizeof(void*)*7 + 1, x_44);
x_46 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_45, x_1, x_12, x_6, x_14);
return x_46;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_8);
if (x_69 == 0)
{
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_8, 0);
x_71 = lean_ctor_get(x_8, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_8);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_indentExpr(x_6);
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_MessageData_ofList___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_KernelException_toMessageData___closed__12;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l_Lean_indentExpr(x_13);
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Term_throwError___rarg(x_15, x_4, x_5);
return x_16;
}
}
lean_object* l___private_Lean_Elab_App_12__throwLValError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_12__throwLValError___rarg), 5, 0);
return x_2;
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
x_1 = lean_mk_string("invalid projection, structure has only ");
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
x_1 = lean_mk_string(" field(s)");
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
x_1 = lean_mk_string("invalid projection, structure expected");
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
lean_object* l___private_Lean_Elab_App_13__resolveLValAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_12) == 4)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_42; 
x_17 = l_Lean_Elab_Term_getEnv___rarg(x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
lean_inc(x_13);
lean_inc(x_18);
x_42 = l_Lean_isStructureLike(x_18, x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
x_43 = l___private_Lean_Elab_App_13__resolveLValAux___closed__15;
x_44 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_43, x_4, x_19);
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
else
{
x_21 = x_19;
goto block_41;
}
block_41:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_inc(x_13);
lean_inc(x_18);
x_22 = l_Lean_getStructureFields(x_18, x_13);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_14, x_23);
lean_dec(x_14);
x_25 = lean_array_get_size(x_22);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_13);
x_27 = l_Nat_repr(x_25);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l___private_Lean_Elab_App_13__resolveLValAux___closed__9;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l___private_Lean_Elab_App_13__resolveLValAux___closed__12;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_33, x_4, x_21);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_25);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_13);
x_35 = l_Lean_isStructure(x_18, x_13);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_24);
if (lean_is_scalar(x_20)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_20;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_array_fget(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
lean_inc(x_13);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_13);
lean_ctor_set(x_39, 2, x_38);
if (lean_is_scalar(x_20)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_20;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_21);
return x_40;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_49 = l___private_Lean_Elab_App_13__resolveLValAux___closed__18;
x_50 = l_Lean_Elab_Term_throwError___rarg(x_49, x_4, x_5);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
case 1:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_12, 0);
lean_inc(x_55);
lean_dec(x_12);
x_56 = lean_ctor_get(x_3, 0);
lean_inc(x_56);
lean_dec(x_3);
x_57 = l_Lean_Elab_Term_getEnv___rarg(x_5);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_55);
lean_inc(x_59);
x_61 = l_Lean_isStructure(x_59, x_55);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_free_object(x_57);
x_62 = lean_box(0);
lean_inc(x_56);
x_63 = lean_name_mk_string(x_62, x_56);
x_64 = l_Lean_Name_append___main(x_55, x_63);
x_65 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_60);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_64);
x_68 = l_Lean_Name_replacePrefix___main(x_64, x_66, x_62);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_getLCtx(x_4, x_67);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_local_ctx_find_from_user_name(x_71, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_inc(x_64);
lean_inc(x_59);
x_74 = lean_environment_find(x_59, x_64);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_inc(x_64);
lean_inc(x_59);
x_75 = l_Lean_mkPrivateName(x_59, x_64);
lean_inc(x_75);
x_76 = lean_environment_find(x_59, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_75);
lean_free_object(x_69);
lean_dec(x_55);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_56);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_80 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_82 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_83, 0, x_64);
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Core_getConstInfo___closed__5;
x_86 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_86, x_4, x_72);
return x_87;
}
else
{
lean_object* x_88; 
lean_dec(x_76);
lean_dec(x_64);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_55);
lean_ctor_set(x_88, 1, x_75);
lean_ctor_set(x_69, 0, x_88);
return x_69;
}
}
else
{
lean_object* x_89; 
lean_dec(x_74);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_55);
lean_ctor_set(x_89, 1, x_64);
lean_ctor_set(x_69, 0, x_89);
return x_69;
}
}
else
{
lean_object* x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
lean_dec(x_73);
x_91 = l_Lean_LocalDecl_binderInfo(x_90);
x_92 = 4;
x_93 = l_Lean_BinderInfo_beq(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_90);
lean_inc(x_64);
lean_inc(x_59);
x_94 = lean_environment_find(x_59, x_64);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_inc(x_64);
lean_inc(x_59);
x_95 = l_Lean_mkPrivateName(x_59, x_64);
lean_inc(x_95);
x_96 = lean_environment_find(x_59, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_95);
lean_free_object(x_69);
lean_dec(x_55);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_56);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_100 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_102 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_103, 0, x_64);
x_104 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_Core_getConstInfo___closed__5;
x_106 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_106, x_4, x_72);
return x_107;
}
else
{
lean_object* x_108; 
lean_dec(x_96);
lean_dec(x_64);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_55);
lean_ctor_set(x_108, 1, x_95);
lean_ctor_set(x_69, 0, x_108);
return x_69;
}
}
else
{
lean_object* x_109; 
lean_dec(x_94);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_55);
lean_ctor_set(x_109, 1, x_64);
lean_ctor_set(x_69, 0, x_109);
return x_69;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = l_Lean_LocalDecl_toExpr(x_90);
lean_dec(x_90);
x_111 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_111, 0, x_55);
lean_ctor_set(x_111, 1, x_64);
lean_ctor_set(x_111, 2, x_110);
lean_ctor_set(x_69, 0, x_111);
return x_69;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_69, 0);
x_113 = lean_ctor_get(x_69, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_69);
x_114 = lean_local_ctx_find_from_user_name(x_112, x_68);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
lean_inc(x_64);
lean_inc(x_59);
x_115 = lean_environment_find(x_59, x_64);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_inc(x_64);
lean_inc(x_59);
x_116 = l_Lean_mkPrivateName(x_59, x_64);
lean_inc(x_116);
x_117 = lean_environment_find(x_59, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_116);
lean_dec(x_55);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_56);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_121 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_123 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_124, 0, x_64);
x_125 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Core_getConstInfo___closed__5;
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_127, x_4, x_113);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_117);
lean_dec(x_64);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_55);
lean_ctor_set(x_129, 1, x_116);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_113);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_115);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_55);
lean_ctor_set(x_131, 1, x_64);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_113);
return x_132;
}
}
else
{
lean_object* x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_114, 0);
lean_inc(x_133);
lean_dec(x_114);
x_134 = l_Lean_LocalDecl_binderInfo(x_133);
x_135 = 4;
x_136 = l_Lean_BinderInfo_beq(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_133);
lean_inc(x_64);
lean_inc(x_59);
x_137 = lean_environment_find(x_59, x_64);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_inc(x_64);
lean_inc(x_59);
x_138 = l_Lean_mkPrivateName(x_59, x_64);
lean_inc(x_138);
x_139 = lean_environment_find(x_59, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_138);
lean_dec(x_55);
x_140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_140, 0, x_56);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_143 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_145 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_146, 0, x_64);
x_147 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_Core_getConstInfo___closed__5;
x_149 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_149, x_4, x_113);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_139);
lean_dec(x_64);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_55);
lean_ctor_set(x_151, 1, x_138);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_113);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_137);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_55);
lean_ctor_set(x_153, 1, x_64);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_113);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_155 = l_Lean_LocalDecl_toExpr(x_133);
lean_dec(x_133);
x_156 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_156, 0, x_55);
lean_ctor_set(x_156, 1, x_64);
lean_ctor_set(x_156, 2, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_113);
return x_157;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_box(0);
lean_inc(x_56);
x_159 = lean_name_mk_string(x_158, x_56);
lean_inc(x_55);
lean_inc(x_59);
x_160 = l_Lean_findField_x3f___main(x_59, x_55, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
lean_free_object(x_57);
x_161 = l_Lean_Name_append___main(x_55, x_159);
x_162 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_60);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
lean_inc(x_161);
x_165 = l_Lean_Name_replacePrefix___main(x_161, x_163, x_158);
lean_dec(x_163);
x_166 = l_Lean_Elab_Term_getLCtx(x_4, x_164);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
x_170 = lean_local_ctx_find_from_user_name(x_168, x_165);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
lean_inc(x_161);
lean_inc(x_59);
x_171 = lean_environment_find(x_59, x_161);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_inc(x_161);
lean_inc(x_59);
x_172 = l_Lean_mkPrivateName(x_59, x_161);
lean_inc(x_172);
x_173 = lean_environment_find(x_59, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_172);
lean_free_object(x_166);
lean_dec(x_55);
x_174 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_174, 0, x_56);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_177 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_179 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_180, 0, x_161);
x_181 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Core_getConstInfo___closed__5;
x_183 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_183, x_4, x_169);
return x_184;
}
else
{
lean_object* x_185; 
lean_dec(x_173);
lean_dec(x_161);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_185, 0, x_55);
lean_ctor_set(x_185, 1, x_172);
lean_ctor_set(x_166, 0, x_185);
return x_166;
}
}
else
{
lean_object* x_186; 
lean_dec(x_171);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_186, 0, x_55);
lean_ctor_set(x_186, 1, x_161);
lean_ctor_set(x_166, 0, x_186);
return x_166;
}
}
else
{
lean_object* x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_170, 0);
lean_inc(x_187);
lean_dec(x_170);
x_188 = l_Lean_LocalDecl_binderInfo(x_187);
x_189 = 4;
x_190 = l_Lean_BinderInfo_beq(x_188, x_189);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_187);
lean_inc(x_161);
lean_inc(x_59);
x_191 = lean_environment_find(x_59, x_161);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_inc(x_161);
lean_inc(x_59);
x_192 = l_Lean_mkPrivateName(x_59, x_161);
lean_inc(x_192);
x_193 = lean_environment_find(x_59, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_192);
lean_free_object(x_166);
lean_dec(x_55);
x_194 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_194, 0, x_56);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_197 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_199 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_200, 0, x_161);
x_201 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_Core_getConstInfo___closed__5;
x_203 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_203, x_4, x_169);
return x_204;
}
else
{
lean_object* x_205; 
lean_dec(x_193);
lean_dec(x_161);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_55);
lean_ctor_set(x_205, 1, x_192);
lean_ctor_set(x_166, 0, x_205);
return x_166;
}
}
else
{
lean_object* x_206; 
lean_dec(x_191);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_55);
lean_ctor_set(x_206, 1, x_161);
lean_ctor_set(x_166, 0, x_206);
return x_166;
}
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_207 = l_Lean_LocalDecl_toExpr(x_187);
lean_dec(x_187);
x_208 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_208, 0, x_55);
lean_ctor_set(x_208, 1, x_161);
lean_ctor_set(x_208, 2, x_207);
lean_ctor_set(x_166, 0, x_208);
return x_166;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_166, 0);
x_210 = lean_ctor_get(x_166, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_166);
x_211 = lean_local_ctx_find_from_user_name(x_209, x_165);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
lean_inc(x_161);
lean_inc(x_59);
x_212 = lean_environment_find(x_59, x_161);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_inc(x_161);
lean_inc(x_59);
x_213 = l_Lean_mkPrivateName(x_59, x_161);
lean_inc(x_213);
x_214 = lean_environment_find(x_59, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_213);
lean_dec(x_55);
x_215 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_215, 0, x_56);
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_218 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_220 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_221, 0, x_161);
x_222 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = l_Lean_Core_getConstInfo___closed__5;
x_224 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_224, x_4, x_210);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_214);
lean_dec(x_161);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_55);
lean_ctor_set(x_226, 1, x_213);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_210);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_212);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_55);
lean_ctor_set(x_228, 1, x_161);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_210);
return x_229;
}
}
else
{
lean_object* x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; 
x_230 = lean_ctor_get(x_211, 0);
lean_inc(x_230);
lean_dec(x_211);
x_231 = l_Lean_LocalDecl_binderInfo(x_230);
x_232 = 4;
x_233 = l_Lean_BinderInfo_beq(x_231, x_232);
if (x_233 == 0)
{
lean_object* x_234; 
lean_dec(x_230);
lean_inc(x_161);
lean_inc(x_59);
x_234 = lean_environment_find(x_59, x_161);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; 
lean_inc(x_161);
lean_inc(x_59);
x_235 = l_Lean_mkPrivateName(x_59, x_161);
lean_inc(x_235);
x_236 = lean_environment_find(x_59, x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_235);
lean_dec(x_55);
x_237 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_237, 0, x_56);
x_238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_239 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_240 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
x_241 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_242 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_243, 0, x_161);
x_244 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Lean_Core_getConstInfo___closed__5;
x_246 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_246, x_4, x_210);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_236);
lean_dec(x_161);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_248 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_248, 0, x_55);
lean_ctor_set(x_248, 1, x_235);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_210);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_234);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_250, 0, x_55);
lean_ctor_set(x_250, 1, x_161);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_210);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_252 = l_Lean_LocalDecl_toExpr(x_230);
lean_dec(x_230);
x_253 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_253, 0, x_55);
lean_ctor_set(x_253, 1, x_161);
lean_ctor_set(x_253, 2, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_210);
return x_254;
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_255 = lean_ctor_get(x_160, 0);
lean_inc(x_255);
lean_dec(x_160);
x_256 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_55);
lean_ctor_set(x_256, 2, x_159);
lean_ctor_set(x_57, 0, x_256);
return x_57;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_ctor_get(x_57, 0);
x_258 = lean_ctor_get(x_57, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_57);
lean_inc(x_55);
lean_inc(x_257);
x_259 = l_Lean_isStructure(x_257, x_55);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_260 = lean_box(0);
lean_inc(x_56);
x_261 = lean_name_mk_string(x_260, x_56);
x_262 = l_Lean_Name_append___main(x_55, x_261);
x_263 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_258);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_262);
x_266 = l_Lean_Name_replacePrefix___main(x_262, x_264, x_260);
lean_dec(x_264);
x_267 = l_Lean_Elab_Term_getLCtx(x_4, x_265);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
x_271 = lean_local_ctx_find_from_user_name(x_268, x_266);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
lean_inc(x_262);
lean_inc(x_257);
x_272 = lean_environment_find(x_257, x_262);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
lean_inc(x_262);
lean_inc(x_257);
x_273 = l_Lean_mkPrivateName(x_257, x_262);
lean_inc(x_273);
x_274 = lean_environment_find(x_257, x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_273);
lean_dec(x_270);
lean_dec(x_55);
x_275 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_275, 0, x_56);
x_276 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_276, 0, x_275);
x_277 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_278 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_280 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_281, 0, x_262);
x_282 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_Core_getConstInfo___closed__5;
x_284 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_284, x_4, x_269);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_274);
lean_dec(x_262);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_286 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_286, 0, x_55);
lean_ctor_set(x_286, 1, x_273);
if (lean_is_scalar(x_270)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_270;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_269);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_272);
lean_dec(x_257);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_288 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_288, 0, x_55);
lean_ctor_set(x_288, 1, x_262);
if (lean_is_scalar(x_270)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_270;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_269);
return x_289;
}
}
else
{
lean_object* x_290; uint8_t x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_271, 0);
lean_inc(x_290);
lean_dec(x_271);
x_291 = l_Lean_LocalDecl_binderInfo(x_290);
x_292 = 4;
x_293 = l_Lean_BinderInfo_beq(x_291, x_292);
if (x_293 == 0)
{
lean_object* x_294; 
lean_dec(x_290);
lean_inc(x_262);
lean_inc(x_257);
x_294 = lean_environment_find(x_257, x_262);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; 
lean_inc(x_262);
lean_inc(x_257);
x_295 = l_Lean_mkPrivateName(x_257, x_262);
lean_inc(x_295);
x_296 = lean_environment_find(x_257, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_295);
lean_dec(x_270);
lean_dec(x_55);
x_297 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_297, 0, x_56);
x_298 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_299 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_300 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
x_301 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_302 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_303, 0, x_262);
x_304 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Core_getConstInfo___closed__5;
x_306 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_306, x_4, x_269);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec(x_296);
lean_dec(x_262);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_308 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_308, 0, x_55);
lean_ctor_set(x_308, 1, x_295);
if (lean_is_scalar(x_270)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_270;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_269);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_294);
lean_dec(x_257);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_310 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_310, 0, x_55);
lean_ctor_set(x_310, 1, x_262);
if (lean_is_scalar(x_270)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_270;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_269);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_257);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_312 = l_Lean_LocalDecl_toExpr(x_290);
lean_dec(x_290);
x_313 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_313, 0, x_55);
lean_ctor_set(x_313, 1, x_262);
lean_ctor_set(x_313, 2, x_312);
if (lean_is_scalar(x_270)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_270;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_269);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_box(0);
lean_inc(x_56);
x_316 = lean_name_mk_string(x_315, x_56);
lean_inc(x_55);
lean_inc(x_257);
x_317 = l_Lean_findField_x3f___main(x_257, x_55, x_316);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_318 = l_Lean_Name_append___main(x_55, x_316);
x_319 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_258);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
lean_inc(x_318);
x_322 = l_Lean_Name_replacePrefix___main(x_318, x_320, x_315);
lean_dec(x_320);
x_323 = l_Lean_Elab_Term_getLCtx(x_4, x_321);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_326 = x_323;
} else {
 lean_dec_ref(x_323);
 x_326 = lean_box(0);
}
x_327 = lean_local_ctx_find_from_user_name(x_324, x_322);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; 
lean_inc(x_318);
lean_inc(x_257);
x_328 = lean_environment_find(x_257, x_318);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_inc(x_318);
lean_inc(x_257);
x_329 = l_Lean_mkPrivateName(x_257, x_318);
lean_inc(x_329);
x_330 = lean_environment_find(x_257, x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_329);
lean_dec(x_326);
lean_dec(x_55);
x_331 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_331, 0, x_56);
x_332 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_332, 0, x_331);
x_333 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_334 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_332);
x_335 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_336 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
x_337 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_337, 0, x_318);
x_338 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Lean_Core_getConstInfo___closed__5;
x_340 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
x_341 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_340, x_4, x_325);
return x_341;
}
else
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_330);
lean_dec(x_318);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_342 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_342, 0, x_55);
lean_ctor_set(x_342, 1, x_329);
if (lean_is_scalar(x_326)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_326;
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_325);
return x_343;
}
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_328);
lean_dec(x_257);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_344 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_344, 0, x_55);
lean_ctor_set(x_344, 1, x_318);
if (lean_is_scalar(x_326)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_326;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_325);
return x_345;
}
}
else
{
lean_object* x_346; uint8_t x_347; uint8_t x_348; uint8_t x_349; 
x_346 = lean_ctor_get(x_327, 0);
lean_inc(x_346);
lean_dec(x_327);
x_347 = l_Lean_LocalDecl_binderInfo(x_346);
x_348 = 4;
x_349 = l_Lean_BinderInfo_beq(x_347, x_348);
if (x_349 == 0)
{
lean_object* x_350; 
lean_dec(x_346);
lean_inc(x_318);
lean_inc(x_257);
x_350 = lean_environment_find(x_257, x_318);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; 
lean_inc(x_318);
lean_inc(x_257);
x_351 = l_Lean_mkPrivateName(x_257, x_318);
lean_inc(x_351);
x_352 = lean_environment_find(x_257, x_351);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_351);
lean_dec(x_326);
lean_dec(x_55);
x_353 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_353, 0, x_56);
x_354 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_354, 0, x_353);
x_355 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_356 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
x_357 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_358 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_359, 0, x_318);
x_360 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
x_361 = l_Lean_Core_getConstInfo___closed__5;
x_362 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
x_363 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_362, x_4, x_325);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; 
lean_dec(x_352);
lean_dec(x_318);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_364 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_364, 0, x_55);
lean_ctor_set(x_364, 1, x_351);
if (lean_is_scalar(x_326)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_326;
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_325);
return x_365;
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_350);
lean_dec(x_257);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_366 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_366, 0, x_55);
lean_ctor_set(x_366, 1, x_318);
if (lean_is_scalar(x_326)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_326;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_325);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_257);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_368 = l_Lean_LocalDecl_toExpr(x_346);
lean_dec(x_346);
x_369 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_369, 0, x_55);
lean_ctor_set(x_369, 1, x_318);
lean_ctor_set(x_369, 2, x_368);
if (lean_is_scalar(x_326)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_326;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_325);
return x_370;
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_257);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_371 = lean_ctor_get(x_317, 0);
lean_inc(x_371);
lean_dec(x_317);
x_372 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_55);
lean_ctor_set(x_372, 2, x_316);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_258);
return x_373;
}
}
}
}
default: 
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_374 = lean_ctor_get(x_12, 0);
lean_inc(x_374);
lean_dec(x_12);
x_375 = lean_ctor_get(x_3, 0);
lean_inc(x_375);
lean_dec(x_3);
x_376 = l_Lean_Elab_Term_getEnv___rarg(x_5);
x_377 = !lean_is_exclusive(x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_378 = lean_ctor_get(x_376, 0);
x_379 = lean_ctor_get(x_376, 1);
x_380 = l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
x_381 = lean_name_mk_string(x_374, x_380);
lean_inc(x_381);
x_382 = lean_environment_find(x_378, x_381);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_free_object(x_376);
lean_dec(x_375);
x_383 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_383, 0, x_381);
x_384 = l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
x_385 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l_Lean_Core_getConstInfo___closed__5;
x_387 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_387, x_4, x_379);
return x_388;
}
else
{
lean_object* x_389; 
lean_dec(x_382);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_389 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_389, 0, x_381);
lean_ctor_set(x_389, 1, x_375);
lean_ctor_set(x_376, 0, x_389);
return x_376;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_390 = lean_ctor_get(x_376, 0);
x_391 = lean_ctor_get(x_376, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_376);
x_392 = l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
x_393 = lean_name_mk_string(x_374, x_392);
lean_inc(x_393);
x_394 = lean_environment_find(x_390, x_393);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_375);
x_395 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_395, 0, x_393);
x_396 = l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
x_397 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_395);
x_398 = l_Lean_Core_getConstInfo___closed__5;
x_399 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
x_400 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_399, x_4, x_391);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; 
lean_dec(x_394);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_401 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_401, 0, x_393);
lean_ctor_set(x_401, 1, x_375);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_391);
return x_402;
}
}
}
}
}
else
{
lean_object* x_403; 
lean_dec(x_12);
x_403 = lean_box(0);
x_6 = x_403;
goto block_11;
}
block_11:
{
lean_dec(x_6);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = l___private_Lean_Elab_App_13__resolveLValAux___closed__6;
x_8 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_7, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = l___private_Lean_Elab_App_13__resolveLValAux___closed__3;
x_10 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_9, x_4, x_5);
return x_10;
}
}
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_1);
x_12 = l_Std_PersistentArray_push___rarg(x_11, x_1);
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
x_22 = l_Std_PersistentArray_push___rarg(x_18, x_1);
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
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_Elab_Term_whnfCore(x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_8);
x_10 = l_Lean_Elab_Term_tryPostponeIfMVar(x_8, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_App_13__resolveLValAux(x_1, x_8, x_2, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
x_17 = l_Lean_Elab_Term_unfoldDefinition_x3f(x_8, x_5, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_forMAux___main___at___private_Lean_Elab_App_14__resolveLValLoop___main___spec__1(x_16, x_4, x_20, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_13);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_array_push(x_4, x_16);
x_3 = x_27;
x_4 = x_28;
x_6 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_12, 0);
lean_dec(x_35);
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_13);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_10);
if (x_38 == 0)
{
return x_10;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_10, 0);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_10);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
return x_7;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
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
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_App_14__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_App_15__resolveLVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Elab_Term_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Array_empty___closed__1;
x_9 = l___private_Lean_Elab_App_14__resolveLValLoop___main(x_1, x_2, x_6, x_8, x_3, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_box(0);
lean_inc(x_3);
x_9 = l_Lean_Elab_Term_mkConst(x_6, x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_mkOptionalNode___closed__2;
x_16 = lean_array_push(x_15, x_14);
x_17 = lean_box(0);
x_18 = l_Array_empty___closed__1;
x_19 = 0;
lean_inc(x_3);
x_20 = l___private_Lean_Elab_App_11__elabAppArgs(x_10, x_16, x_18, x_17, x_19, x_3, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_1 = x_21;
x_2 = x_7;
x_4 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
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
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
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
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Term_getEnv___rarg(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_getPathToBaseStructure_x3f(x_7, x_1, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = l___private_Lean_Elab_App_16__mkBaseProjections___closed__3;
x_11 = l_Lean_Elab_Term_throwError___rarg(x_10, x_4, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1(x_3, x_12, x_4, x_8);
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_App_16__mkBaseProjections(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
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
lean_object* l___private_Lean_Elab_App_17__addLValArg___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint8_t x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_7, 2);
x_25 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
x_26 = (uint8_t)((x_25 << 24) >> 61);
x_27 = l_Lean_BinderInfo_isExplicit(x_26);
if (x_27 == 0)
{
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_17__addLValArg___main___spec__1(x_22, x_6, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Expr_consumeMData___main(x_23);
x_32 = l_Lean_Expr_isAppOf(x_31, x_1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_array_get_size(x_4);
x_34 = lean_nat_dec_lt(x_5, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_2);
x_36 = l___private_Lean_Elab_App_17__addLValArg___main___closed__12;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Core_getConstInfo___closed__5;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Term_throwError___rarg(x_39, x_8, x_9);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_5, x_41);
lean_dec(x_5);
x_5 = x_42;
x_7 = x_24;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_3);
x_45 = l_Array_insertAt___rarg(x_4, x_5, x_44);
lean_dec(x_5);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_9);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_30, 0);
lean_inc(x_47);
lean_dec(x_30);
x_48 = l_Array_eraseIdx___rarg(x_6, x_47);
lean_dec(x_47);
x_6 = x_48;
x_7 = x_24;
goto _start;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = lean_box(0);
x_10 = x_50;
goto block_21;
}
block_21:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = l___private_Lean_Elab_App_17__addLValArg___main___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Elab_App_17__addLValArg___main___closed__6;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Elab_App_17__addLValArg___main___closed__9;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Term_throwError___rarg(x_19, x_8, x_9);
return x_20;
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
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_17__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_17__addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_17__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_17__addLValArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_17__addLValArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
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
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_11__elabAppArgs(x_5, x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
lean_inc(x_7);
lean_inc(x_5);
x_12 = l___private_Lean_Elab_App_15__resolveLVal(x_5, x_10, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
lean_dec(x_13);
lean_inc(x_7);
x_18 = l___private_Lean_Elab_App_16__mkBaseProjections(x_15, x_16, x_5, x_7, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Name_append___main(x_15, x_17);
lean_dec(x_15);
x_22 = lean_box(0);
lean_inc(x_7);
x_23 = l_Lean_Elab_Term_mkConst(x_21, x_22, x_7, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_List_isEmpty___rarg(x_11);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_19);
x_28 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_mkOptionalNode___closed__2;
x_31 = lean_array_push(x_30, x_29);
x_32 = lean_box(0);
x_33 = l_Array_empty___closed__1;
x_34 = 0;
lean_inc(x_7);
x_35 = l___private_Lean_Elab_App_11__elabAppArgs(x_24, x_31, x_33, x_32, x_34, x_7, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_5 = x_36;
x_6 = x_11;
x_8 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_19);
x_44 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_inc(x_7);
x_46 = l_Lean_Elab_Term_addNamedArg(x_1, x_45, x_7, x_25);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Lean_Elab_App_11__elabAppArgs(x_24, x_47, x_2, x_3, x_4, x_7, x_48);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
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
uint8_t x_54; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_23);
if (x_54 == 0)
{
return x_23;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_23, 0);
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_23);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_18);
if (x_58 == 0)
{
return x_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
case 1:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_12, 1);
lean_inc(x_62);
lean_dec(x_12);
x_63 = lean_ctor_get(x_13, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_dec(x_13);
x_65 = l_Lean_mkProj(x_63, x_64, x_5);
x_5 = x_65;
x_6 = x_11;
x_8 = x_62;
goto _start;
}
case 2:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
lean_dec(x_12);
x_68 = lean_ctor_get(x_13, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_13, 1);
lean_inc(x_69);
lean_dec(x_13);
x_70 = lean_box(0);
lean_inc(x_7);
lean_inc(x_69);
x_71 = l_Lean_Elab_Term_mkConst(x_69, x_70, x_7, x_67);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_List_isEmpty___rarg(x_11);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
lean_dec(x_69);
lean_dec(x_68);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_5);
x_76 = l_Lean_mkOptionalNode___closed__2;
x_77 = lean_array_push(x_76, x_75);
x_78 = lean_box(0);
x_79 = l_Array_empty___closed__1;
x_80 = 0;
lean_inc(x_7);
x_81 = l___private_Lean_Elab_App_11__elabAppArgs(x_72, x_79, x_77, x_78, x_80, x_7, x_73);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_5 = x_82;
x_6 = x_11;
x_8 = x_83;
goto _start;
}
else
{
uint8_t x_85; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_81, 0);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_81);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_72);
x_89 = l_Lean_Elab_Term_inferType(x_72, x_7, x_73);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_1);
x_93 = l___private_Lean_Elab_App_17__addLValArg___main(x_68, x_69, x_5, x_2, x_92, x_1, x_90, x_7, x_91);
lean_dec(x_90);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l___private_Lean_Elab_App_11__elabAppArgs(x_72, x_1, x_94, x_3, x_4, x_7, x_95);
return x_96;
}
else
{
uint8_t x_97; 
lean_dec(x_72);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_93, 0);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_93);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_89);
if (x_101 == 0)
{
return x_89;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_89, 0);
x_103 = lean_ctor_get(x_89, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_89);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_71);
if (x_105 == 0)
{
return x_71;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_71, 0);
x_107 = lean_ctor_get(x_71, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_71);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
case 3:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_109 = lean_ctor_get(x_12, 1);
lean_inc(x_109);
lean_dec(x_12);
x_110 = lean_ctor_get(x_13, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_13, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_13, 2);
lean_inc(x_112);
lean_dec(x_13);
x_113 = l_List_isEmpty___rarg(x_11);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
lean_dec(x_111);
lean_dec(x_110);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_5);
x_115 = l_Lean_mkOptionalNode___closed__2;
x_116 = lean_array_push(x_115, x_114);
x_117 = lean_box(0);
x_118 = l_Array_empty___closed__1;
x_119 = 0;
lean_inc(x_7);
x_120 = l___private_Lean_Elab_App_11__elabAppArgs(x_112, x_118, x_116, x_117, x_119, x_7, x_109);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_5 = x_121;
x_6 = x_11;
x_8 = x_122;
goto _start;
}
else
{
uint8_t x_124; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_120);
if (x_124 == 0)
{
return x_120;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_120, 0);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_120);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_112);
x_128 = l_Lean_Elab_Term_inferType(x_112, x_7, x_109);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_1);
x_132 = l___private_Lean_Elab_App_17__addLValArg___main(x_110, x_111, x_5, x_2, x_131, x_1, x_129, x_7, x_130);
lean_dec(x_129);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l___private_Lean_Elab_App_11__elabAppArgs(x_112, x_1, x_133, x_3, x_4, x_7, x_134);
return x_135;
}
else
{
uint8_t x_136; 
lean_dec(x_112);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
return x_132;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_132, 0);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_132);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_128);
if (x_140 == 0)
{
return x_128;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_128, 0);
x_142 = lean_ctor_get(x_128, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_128);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
default: 
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_12, 1);
lean_inc(x_144);
lean_dec(x_12);
x_145 = lean_ctor_get(x_13, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_13, 1);
lean_inc(x_146);
lean_dec(x_13);
x_147 = lean_box(0);
lean_inc(x_7);
x_148 = l_Lean_Elab_Term_mkConst(x_145, x_147, x_7, x_144);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_List_isEmpty___rarg(x_11);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_5);
x_153 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_146);
x_156 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Lean_mkAppStx___closed__9;
x_159 = lean_array_push(x_158, x_154);
x_160 = lean_array_push(x_159, x_157);
x_161 = lean_box(0);
x_162 = l_Array_empty___closed__1;
x_163 = 0;
lean_inc(x_7);
x_164 = l___private_Lean_Elab_App_11__elabAppArgs(x_149, x_160, x_162, x_161, x_163, x_7, x_150);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_5 = x_165;
x_6 = x_11;
x_8 = x_166;
goto _start;
}
else
{
uint8_t x_168; 
lean_dec(x_11);
lean_dec(x_7);
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
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_11);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_5);
x_173 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
lean_inc(x_7);
x_175 = l_Lean_Elab_Term_addNamedArg(x_1, x_174, x_7, x_150);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_146);
x_179 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
lean_inc(x_7);
x_181 = l_Lean_Elab_Term_addNamedArg(x_176, x_180, x_7, x_177);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l___private_Lean_Elab_App_11__elabAppArgs(x_149, x_182, x_2, x_3, x_4, x_7, x_183);
return x_184;
}
else
{
uint8_t x_185; 
lean_dec(x_149);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_181);
if (x_185 == 0)
{
return x_181;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_181, 0);
x_187 = lean_ctor_get(x_181, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_181);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_149);
lean_dec(x_146);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_189 = !lean_is_exclusive(x_175);
if (x_189 == 0)
{
return x_175;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_175, 0);
x_191 = lean_ctor_get(x_175, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_175);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_146);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_148);
if (x_193 == 0)
{
return x_148;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_148, 0);
x_195 = lean_ctor_get(x_148, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_148);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_12);
if (x_197 == 0)
{
return x_12;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_12, 0);
x_199 = lean_ctor_get(x_12, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_12);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l___private_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l___private_Lean_Elab_App_18__elabAppLValsAux(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
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
lean_object* l___private_Lean_Elab_App_19__elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_List_isEmpty___rarg(x_2);
if (x_9 == 0)
{
if (x_6 == 0)
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_18__elabAppLValsAux___main(x_3, x_4, x_5, x_6, x_1, x_2, x_7, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l___private_Lean_Elab_App_19__elabAppLVals___closed__3;
x_12 = l_Lean_Elab_Term_throwError___rarg(x_11, x_7, x_8);
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
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_App_18__elabAppLValsAux___main(x_3, x_4, x_5, x_6, x_1, x_2, x_7, x_8);
return x_17;
}
}
}
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_array_get_size(x_1);
x_6 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(x_1, x_1, x_5, lean_box(0), x_4, x_2, x_3);
return x_6;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabExplicitUnivs(x_1, x_2, x_3);
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_List_map___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__1(x_14);
lean_inc(x_1);
x_16 = l_List_append___rarg(x_15, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l___private_Lean_Elab_App_19__elabAppLVals(x_13, x_16, x_2, x_3, x_4, x_5, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_array_push(x_6, x_17);
x_6 = x_19;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_push(x_6, x_23);
x_6 = x_24;
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_17, 0, x_30);
x_31 = lean_array_push(x_6, x_17);
x_6 = x_31;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_6, x_35);
x_6 = x_36;
x_7 = x_12;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_17, 0);
lean_dec(x_39);
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_17, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_17, 0);
lean_dec(x_44);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_45; 
lean_dec(x_17);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_9);
return x_45;
}
}
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_List_map___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__1(x_14);
lean_inc(x_1);
x_16 = l_List_append___rarg(x_15, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l___private_Lean_Elab_App_19__elabAppLVals(x_13, x_16, x_2, x_3, x_4, x_5, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_array_push(x_6, x_17);
x_6 = x_19;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_push(x_6, x_23);
x_6 = x_24;
x_7 = x_12;
goto _start;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_17, 0, x_30);
x_31 = lean_array_push(x_6, x_17);
x_6 = x_31;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_6, x_35);
x_6 = x_36;
x_7 = x_12;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_17, 0);
lean_dec(x_39);
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_17, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_17, 0);
lean_dec(x_44);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_45; 
lean_dec(x_17);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_9);
return x_45;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_20__elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 2);
x_17 = lean_ctor_get(x_9, 3);
x_18 = lean_ctor_get(x_9, 4);
x_19 = lean_ctor_get(x_9, 5);
x_20 = lean_ctor_get(x_9, 6);
x_21 = lean_ctor_get(x_9, 7);
x_22 = lean_ctor_get(x_9, 8);
x_23 = lean_ctor_get_uint8(x_9, sizeof(void*)*10);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*10 + 1);
x_25 = lean_ctor_get_uint8(x_9, sizeof(void*)*10 + 2);
x_26 = lean_ctor_get(x_9, 9);
x_27 = l_Lean_Elab_replaceRef(x_1, x_26);
lean_dec(x_1);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_ctor_set(x_9, 9, x_27);
x_28 = l_Lean_Elab_Term_resolveName(x_11, x_12, x_2, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_List_lengthAux___main___rarg(x_29, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_15);
lean_ctor_set(x_36, 2, x_16);
lean_ctor_set(x_36, 3, x_17);
lean_ctor_set(x_36, 4, x_18);
lean_ctor_set(x_36, 5, x_19);
lean_ctor_set(x_36, 6, x_20);
lean_ctor_set(x_36, 7, x_21);
lean_ctor_set(x_36, 8, x_22);
lean_ctor_set(x_36, 9, x_26);
lean_ctor_set_uint8(x_36, sizeof(void*)*10, x_23);
lean_ctor_set_uint8(x_36, sizeof(void*)*10 + 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*10 + 2, x_25);
x_37 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_29, x_36, x_30);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_15);
lean_ctor_set(x_38, 2, x_16);
lean_ctor_set(x_38, 3, x_17);
lean_ctor_set(x_38, 4, x_18);
lean_ctor_set(x_38, 5, x_19);
lean_ctor_set(x_38, 6, x_20);
lean_ctor_set(x_38, 7, x_21);
lean_ctor_set(x_38, 8, x_22);
lean_ctor_set(x_38, 9, x_26);
lean_ctor_set_uint8(x_38, sizeof(void*)*10, x_23);
lean_ctor_set_uint8(x_38, sizeof(void*)*10 + 1, x_24);
lean_ctor_set_uint8(x_38, sizeof(void*)*10 + 2, x_25);
x_39 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_29, x_38, x_30);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
return x_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
x_46 = lean_ctor_get(x_9, 2);
x_47 = lean_ctor_get(x_9, 3);
x_48 = lean_ctor_get(x_9, 4);
x_49 = lean_ctor_get(x_9, 5);
x_50 = lean_ctor_get(x_9, 6);
x_51 = lean_ctor_get(x_9, 7);
x_52 = lean_ctor_get(x_9, 8);
x_53 = lean_ctor_get_uint8(x_9, sizeof(void*)*10);
x_54 = lean_ctor_get_uint8(x_9, sizeof(void*)*10 + 1);
x_55 = lean_ctor_get_uint8(x_9, sizeof(void*)*10 + 2);
x_56 = lean_ctor_get(x_9, 9);
lean_inc(x_56);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_57 = l_Lean_Elab_replaceRef(x_1, x_56);
lean_dec(x_1);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_58 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_45);
lean_ctor_set(x_58, 2, x_46);
lean_ctor_set(x_58, 3, x_47);
lean_ctor_set(x_58, 4, x_48);
lean_ctor_set(x_58, 5, x_49);
lean_ctor_set(x_58, 6, x_50);
lean_ctor_set(x_58, 7, x_51);
lean_ctor_set(x_58, 8, x_52);
lean_ctor_set(x_58, 9, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*10, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 1, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 2, x_55);
x_59 = l_Lean_Elab_Term_resolveName(x_11, x_12, x_2, x_58, x_10);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_List_lengthAux___main___rarg(x_60, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_dec_eq(x_63, x_64);
lean_dec(x_63);
if (x_65 == 0)
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_66 = 0;
x_67 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_67, 0, x_44);
lean_ctor_set(x_67, 1, x_45);
lean_ctor_set(x_67, 2, x_46);
lean_ctor_set(x_67, 3, x_47);
lean_ctor_set(x_67, 4, x_48);
lean_ctor_set(x_67, 5, x_49);
lean_ctor_set(x_67, 6, x_50);
lean_ctor_set(x_67, 7, x_51);
lean_ctor_set(x_67, 8, x_52);
lean_ctor_set(x_67, 9, x_56);
lean_ctor_set_uint8(x_67, sizeof(void*)*10, x_53);
lean_ctor_set_uint8(x_67, sizeof(void*)*10 + 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*10 + 2, x_55);
x_68 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_60, x_67, x_61);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_69, 0, x_44);
lean_ctor_set(x_69, 1, x_45);
lean_ctor_set(x_69, 2, x_46);
lean_ctor_set(x_69, 3, x_47);
lean_ctor_set(x_69, 4, x_48);
lean_ctor_set(x_69, 5, x_49);
lean_ctor_set(x_69, 6, x_50);
lean_ctor_set(x_69, 7, x_51);
lean_ctor_set(x_69, 8, x_52);
lean_ctor_set(x_69, 9, x_56);
lean_ctor_set_uint8(x_69, sizeof(void*)*10, x_53);
lean_ctor_set_uint8(x_69, sizeof(void*)*10 + 1, x_54);
lean_ctor_set_uint8(x_69, sizeof(void*)*10 + 2, x_55);
x_70 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_60, x_69, x_61);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_56);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_ctor_get(x_59, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_73 = x_59;
} else {
 lean_dec_ref(x_59);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_10);
return x_75;
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_20__elabAppFnId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Lean_Elab_App_20__elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
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
x_6 = l_Lean_Name_toString___closed__1;
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
x_12 = l_Lean_Name_toString___closed__1;
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_7);
x_13 = lean_nat_dec_lt(x_8, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_fget(x_7, x_8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_8, x_16);
lean_dec(x_8);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l___private_Lean_Elab_App_21__elabAppFn___main(x_15, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_8 = x_17;
x_9 = x_19;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_App_21__elabAppFn___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of named pattern");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_21__elabAppFn___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_21__elabAppFn___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_21__elabAppFn___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_21__elabAppFn___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_Lean_Syntax_getKind(x_1);
x_11 = l_Lean_choiceKind;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_297; lean_object* x_423; uint8_t x_424; 
x_423 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
lean_inc(x_1);
x_424 = l_Lean_Syntax_isOfKind(x_1, x_423);
if (x_424 == 0)
{
uint8_t x_425; 
x_425 = 0;
x_297 = x_425;
goto block_422;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_426 = l_Lean_Syntax_getArgs(x_1);
x_427 = lean_array_get_size(x_426);
lean_dec(x_426);
x_428 = lean_unsigned_to_nat(3u);
x_429 = lean_nat_dec_eq(x_427, x_428);
lean_dec(x_427);
x_297 = x_429;
goto block_422;
}
block_296:
{
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_110; lean_object* x_208; uint8_t x_209; 
x_208 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_1);
x_209 = l_Lean_Syntax_isOfKind(x_1, x_208);
if (x_209 == 0)
{
uint8_t x_210; 
x_210 = 0;
x_110 = x_210;
goto block_207;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_211 = l_Lean_Syntax_getArgs(x_1);
x_212 = lean_array_get_size(x_211);
lean_dec(x_211);
x_213 = lean_unsigned_to_nat(4u);
x_214 = lean_nat_dec_eq(x_212, x_213);
lean_dec(x_212);
x_110 = x_214;
goto block_207;
}
block_109:
{
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(0);
x_18 = 1;
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_Elab_Term_elabTerm(x_1, x_17, x_18, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l___private_Lean_Elab_App_19__elabAppLVals(x_21, x_2, x_3, x_4, x_5, x_6, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_array_push(x_7, x_23);
lean_ctor_set(x_19, 1, x_9);
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
x_29 = lean_array_push(x_7, x_28);
lean_ctor_set(x_19, 1, x_9);
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
x_35 = lean_array_push(x_7, x_23);
lean_ctor_set(x_19, 1, x_9);
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
x_39 = lean_array_push(x_7, x_38);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 0, x_39);
return x_19;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_19);
lean_dec(x_9);
lean_dec(x_7);
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
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_23, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_23, 0);
lean_dec(x_46);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
else
{
lean_object* x_47; 
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_30);
lean_ctor_set(x_47, 1, x_9);
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
x_50 = l___private_Lean_Elab_App_19__elabAppLVals(x_48, x_2, x_3, x_4, x_5, x_6, x_8, x_49);
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
x_55 = lean_array_push(x_7, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_9);
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
x_63 = lean_array_push(x_7, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_9);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_9);
lean_dec(x_7);
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
lean_dec(x_7);
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
lean_ctor_set(x_69, 1, x_9);
return x_69;
}
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_75 = lean_array_push(x_7, x_19);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_9);
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
x_80 = lean_array_push(x_7, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_9);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_9);
lean_dec(x_7);
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
lean_dec(x_7);
x_86 = !lean_is_exclusive(x_19);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_19, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_19, 0);
lean_dec(x_88);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
lean_object* x_89; 
lean_dec(x_19);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_70);
lean_ctor_set(x_89, 1, x_9);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = l_Lean_Syntax_getArg(x_1, x_90);
lean_dec(x_1);
lean_inc(x_91);
x_92 = l_Lean_Syntax_isOfKind(x_91, x_14);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_91);
x_94 = l_Lean_Syntax_isOfKind(x_91, x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_9);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = l_Lean_Syntax_getArgs(x_91);
x_97 = lean_array_get_size(x_96);
lean_dec(x_96);
x_98 = lean_unsigned_to_nat(4u);
x_99 = lean_nat_dec_eq(x_97, x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_9);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Lean_Syntax_getArg(x_91, x_101);
x_103 = l_Lean_Syntax_isOfKind(x_102, x_14);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_9);
return x_104;
}
else
{
uint8_t x_105; 
x_105 = 1;
x_1 = x_91;
x_6 = x_105;
goto _start;
}
}
}
}
else
{
uint8_t x_107; 
x_107 = 1;
x_1 = x_91;
x_6 = x_107;
goto _start;
}
}
}
block_207:
{
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_1);
x_112 = l_Lean_Syntax_isOfKind(x_1, x_111);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = 0;
x_16 = x_113;
goto block_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = l_Lean_Syntax_getArgs(x_1);
x_115 = lean_array_get_size(x_114);
lean_dec(x_114);
x_116 = lean_unsigned_to_nat(2u);
x_117 = lean_nat_dec_eq(x_115, x_116);
lean_dec(x_115);
x_16 = x_117;
goto block_109;
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Lean_Syntax_getArg(x_1, x_118);
lean_inc(x_119);
x_120 = l_Lean_Syntax_isOfKind(x_119, x_14);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; lean_object* x_123; 
lean_dec(x_119);
x_121 = lean_box(0);
x_122 = 1;
lean_inc(x_9);
lean_inc(x_8);
x_123 = l_Lean_Elab_Term_elabTerm(x_1, x_121, x_122, x_8, x_9);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
x_127 = l___private_Lean_Elab_App_19__elabAppLVals(x_125, x_2, x_3, x_4, x_5, x_6, x_8, x_126);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_array_push(x_7, x_127);
lean_ctor_set(x_123, 1, x_9);
lean_ctor_set(x_123, 0, x_129);
return x_123;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_127, 0);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_127);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_7, x_132);
lean_ctor_set(x_123, 1, x_9);
lean_ctor_set(x_123, 0, x_133);
return x_123;
}
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
uint8_t x_136; 
lean_dec(x_134);
x_136 = !lean_is_exclusive(x_127);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_127, 0);
lean_dec(x_137);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
lean_dec(x_135);
lean_ctor_set(x_127, 0, x_138);
x_139 = lean_array_push(x_7, x_127);
lean_ctor_set(x_123, 1, x_9);
lean_ctor_set(x_123, 0, x_139);
return x_123;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_127, 1);
lean_inc(x_140);
lean_dec(x_127);
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
lean_dec(x_135);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_array_push(x_7, x_142);
lean_ctor_set(x_123, 1, x_9);
lean_ctor_set(x_123, 0, x_143);
return x_123;
}
}
else
{
uint8_t x_144; 
lean_free_object(x_123);
lean_dec(x_9);
lean_dec(x_7);
x_144 = !lean_is_exclusive(x_127);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_127, 0);
lean_dec(x_145);
return x_127;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_127, 1);
lean_inc(x_146);
lean_dec(x_127);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_134);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_free_object(x_123);
lean_dec(x_7);
x_148 = !lean_is_exclusive(x_127);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_127, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_127, 0);
lean_dec(x_150);
lean_ctor_set(x_127, 1, x_9);
return x_127;
}
else
{
lean_object* x_151; 
lean_dec(x_127);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_134);
lean_ctor_set(x_151, 1, x_9);
return x_151;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_123, 0);
x_153 = lean_ctor_get(x_123, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_123);
x_154 = l___private_Lean_Elab_App_19__elabAppLVals(x_152, x_2, x_3, x_4, x_5, x_6, x_8, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_array_push(x_7, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_9);
return x_160;
}
else
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_154, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_161);
x_163 = lean_ctor_get(x_154, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_164 = x_154;
} else {
 lean_dec_ref(x_154);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
lean_dec(x_162);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
x_167 = lean_array_push(x_7, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_9);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_9);
lean_dec(x_7);
x_169 = lean_ctor_get(x_154, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_170 = x_154;
} else {
 lean_dec_ref(x_154);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_161);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_7);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_172 = x_154;
} else {
 lean_dec_ref(x_154);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_161);
lean_ctor_set(x_173, 1, x_9);
return x_173;
}
}
}
}
else
{
lean_object* x_174; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = lean_ctor_get(x_123, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
lean_dec(x_174);
x_176 = !lean_is_exclusive(x_123);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_123, 0);
lean_dec(x_177);
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
lean_dec(x_175);
lean_ctor_set(x_123, 0, x_178);
x_179 = lean_array_push(x_7, x_123);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_9);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_123, 1);
lean_inc(x_181);
lean_dec(x_123);
x_182 = lean_ctor_get(x_175, 0);
lean_inc(x_182);
lean_dec(x_175);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = lean_array_push(x_7, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_9);
return x_185;
}
}
else
{
uint8_t x_186; 
lean_dec(x_9);
lean_dec(x_7);
x_186 = !lean_is_exclusive(x_123);
if (x_186 == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_123, 0);
lean_dec(x_187);
return x_123;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_123, 1);
lean_inc(x_188);
lean_dec(x_123);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_174);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_7);
x_190 = !lean_is_exclusive(x_123);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_123, 1);
lean_dec(x_191);
x_192 = lean_ctor_get(x_123, 0);
lean_dec(x_192);
lean_ctor_set(x_123, 1, x_9);
return x_123;
}
else
{
lean_object* x_193; 
lean_dec(x_123);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_174);
lean_ctor_set(x_193, 1, x_9);
return x_193;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_unsigned_to_nat(2u);
x_195 = l_Lean_Syntax_getArg(x_1, x_194);
lean_dec(x_1);
x_196 = l_Lean_Syntax_getArgs(x_195);
lean_dec(x_195);
x_197 = l_Array_empty___closed__1;
x_198 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_194, x_196, x_118, x_197);
lean_dec(x_196);
x_199 = l_Lean_Elab_Term_elabExplicitUnivs(x_198, x_8, x_9);
lean_dec(x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l___private_Lean_Elab_App_20__elabAppFnId(x_119, x_200, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_201);
return x_202;
}
else
{
uint8_t x_203; 
lean_dec(x_119);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_199);
if (x_203 == 0)
{
return x_199;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_199, 0);
x_205 = lean_ctor_get(x_199, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_199);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_box(0);
x_216 = l___private_Lean_Elab_App_20__elabAppFnId(x_1, x_215, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_217 = lean_unsigned_to_nat(0u);
x_218 = l_Lean_Syntax_getArg(x_1, x_217);
x_219 = l_Lean_identKind___closed__2;
x_220 = l_Lean_Syntax_isOfKind(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; uint8_t x_222; lean_object* x_223; 
x_221 = lean_box(0);
x_222 = 1;
lean_inc(x_9);
lean_inc(x_8);
x_223 = l_Lean_Elab_Term_elabTerm(x_1, x_221, x_222, x_8, x_9);
if (lean_obj_tag(x_223) == 0)
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_223, 0);
x_226 = lean_ctor_get(x_223, 1);
x_227 = l___private_Lean_Elab_App_19__elabAppLVals(x_225, x_2, x_3, x_4, x_5, x_6, x_8, x_226);
if (lean_obj_tag(x_227) == 0)
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; 
x_229 = lean_array_push(x_7, x_227);
lean_ctor_set(x_223, 1, x_9);
lean_ctor_set(x_223, 0, x_229);
return x_223;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_227, 0);
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_227);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_array_push(x_7, x_232);
lean_ctor_set(x_223, 1, x_9);
lean_ctor_set(x_223, 0, x_233);
return x_223;
}
}
else
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_227, 0);
lean_inc(x_234);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
uint8_t x_236; 
lean_dec(x_234);
x_236 = !lean_is_exclusive(x_227);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_227, 0);
lean_dec(x_237);
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
lean_dec(x_235);
lean_ctor_set(x_227, 0, x_238);
x_239 = lean_array_push(x_7, x_227);
lean_ctor_set(x_223, 1, x_9);
lean_ctor_set(x_223, 0, x_239);
return x_223;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = lean_ctor_get(x_227, 1);
lean_inc(x_240);
lean_dec(x_227);
x_241 = lean_ctor_get(x_235, 0);
lean_inc(x_241);
lean_dec(x_235);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = lean_array_push(x_7, x_242);
lean_ctor_set(x_223, 1, x_9);
lean_ctor_set(x_223, 0, x_243);
return x_223;
}
}
else
{
uint8_t x_244; 
lean_free_object(x_223);
lean_dec(x_9);
lean_dec(x_7);
x_244 = !lean_is_exclusive(x_227);
if (x_244 == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_227, 0);
lean_dec(x_245);
return x_227;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_227, 1);
lean_inc(x_246);
lean_dec(x_227);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_234);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
else
{
uint8_t x_248; 
lean_free_object(x_223);
lean_dec(x_7);
x_248 = !lean_is_exclusive(x_227);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_227, 1);
lean_dec(x_249);
x_250 = lean_ctor_get(x_227, 0);
lean_dec(x_250);
lean_ctor_set(x_227, 1, x_9);
return x_227;
}
else
{
lean_object* x_251; 
lean_dec(x_227);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_234);
lean_ctor_set(x_251, 1, x_9);
return x_251;
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_223, 0);
x_253 = lean_ctor_get(x_223, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_223);
x_254 = l___private_Lean_Elab_App_19__elabAppLVals(x_252, x_2, x_3, x_4, x_5, x_6, x_8, x_253);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
x_259 = lean_array_push(x_7, x_258);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_9);
return x_260;
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_254, 0);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_261);
x_263 = lean_ctor_get(x_254, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_264 = x_254;
} else {
 lean_dec_ref(x_254);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
lean_dec(x_262);
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_263);
x_267 = lean_array_push(x_7, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_9);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_9);
lean_dec(x_7);
x_269 = lean_ctor_get(x_254, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_270 = x_254;
} else {
 lean_dec_ref(x_254);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_261);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_7);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_272 = x_254;
} else {
 lean_dec_ref(x_254);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_261);
lean_ctor_set(x_273, 1, x_9);
return x_273;
}
}
}
}
else
{
lean_object* x_274; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_274 = lean_ctor_get(x_223, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_obj_tag(x_275) == 0)
{
uint8_t x_276; 
lean_dec(x_274);
x_276 = !lean_is_exclusive(x_223);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = lean_ctor_get(x_223, 0);
lean_dec(x_277);
x_278 = lean_ctor_get(x_275, 0);
lean_inc(x_278);
lean_dec(x_275);
lean_ctor_set(x_223, 0, x_278);
x_279 = lean_array_push(x_7, x_223);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_9);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_223, 1);
lean_inc(x_281);
lean_dec(x_223);
x_282 = lean_ctor_get(x_275, 0);
lean_inc(x_282);
lean_dec(x_275);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_281);
x_284 = lean_array_push(x_7, x_283);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_9);
return x_285;
}
}
else
{
uint8_t x_286; 
lean_dec(x_9);
lean_dec(x_7);
x_286 = !lean_is_exclusive(x_223);
if (x_286 == 0)
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_223, 0);
lean_dec(x_287);
return x_223;
}
else
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_223, 1);
lean_inc(x_288);
lean_dec(x_223);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_274);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
else
{
uint8_t x_290; 
lean_dec(x_7);
x_290 = !lean_is_exclusive(x_223);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_223, 1);
lean_dec(x_291);
x_292 = lean_ctor_get(x_223, 0);
lean_dec(x_292);
lean_ctor_set(x_223, 1, x_9);
return x_223;
}
else
{
lean_object* x_293; 
lean_dec(x_223);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_274);
lean_ctor_set(x_293, 1, x_9);
return x_293;
}
}
}
}
else
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = l___private_Lean_Elab_App_21__elabAppFn___main___closed__3;
x_295 = l_Lean_Elab_Term_throwError___rarg(x_294, x_8, x_9);
return x_295;
}
}
}
block_422:
{
if (x_297 == 0)
{
lean_object* x_298; uint8_t x_299; 
x_298 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_inc(x_1);
x_299 = l_Lean_Syntax_isOfKind(x_1, x_298);
if (x_299 == 0)
{
lean_object* x_300; uint8_t x_301; 
x_300 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
lean_inc(x_1);
x_301 = l_Lean_Syntax_isOfKind(x_1, x_300);
if (x_301 == 0)
{
uint8_t x_302; 
x_302 = 0;
x_13 = x_302;
goto block_296;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_303 = l_Lean_Syntax_getArgs(x_1);
x_304 = lean_array_get_size(x_303);
lean_dec(x_303);
x_305 = lean_unsigned_to_nat(3u);
x_306 = lean_nat_dec_eq(x_304, x_305);
lean_dec(x_304);
x_13 = x_306;
goto block_296;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_307 = l_Lean_Syntax_getArgs(x_1);
x_308 = lean_array_get_size(x_307);
lean_dec(x_307);
x_309 = lean_unsigned_to_nat(4u);
x_310 = lean_nat_dec_eq(x_308, x_309);
if (x_310 == 0)
{
lean_object* x_311; uint8_t x_312; 
x_311 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
lean_inc(x_1);
x_312 = l_Lean_Syntax_isOfKind(x_1, x_311);
if (x_312 == 0)
{
uint8_t x_313; 
lean_dec(x_308);
x_313 = 0;
x_13 = x_313;
goto block_296;
}
else
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_unsigned_to_nat(3u);
x_315 = lean_nat_dec_eq(x_308, x_314);
lean_dec(x_308);
x_13 = x_315;
goto block_296;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_308);
x_316 = lean_unsigned_to_nat(0u);
x_317 = l_Lean_Syntax_getArg(x_1, x_316);
x_318 = lean_unsigned_to_nat(2u);
x_319 = l_Lean_Syntax_getArg(x_1, x_318);
lean_dec(x_1);
x_320 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_320, 0, x_319);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_2);
x_1 = x_317;
x_2 = x_321;
goto _start;
}
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_323 = lean_unsigned_to_nat(0u);
x_324 = l_Lean_Syntax_getArg(x_1, x_323);
x_325 = lean_unsigned_to_nat(2u);
x_326 = l_Lean_Syntax_getArg(x_1, x_325);
x_327 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_326);
x_328 = l_Lean_Syntax_isOfKind(x_326, x_327);
if (x_328 == 0)
{
lean_object* x_329; uint8_t x_330; 
x_329 = l_Lean_identKind___closed__2;
lean_inc(x_326);
x_330 = l_Lean_Syntax_isOfKind(x_326, x_329);
if (x_330 == 0)
{
lean_object* x_331; uint8_t x_332; lean_object* x_333; 
lean_dec(x_326);
lean_dec(x_324);
x_331 = lean_box(0);
x_332 = 1;
lean_inc(x_9);
lean_inc(x_8);
x_333 = l_Lean_Elab_Term_elabTerm(x_1, x_331, x_332, x_8, x_9);
if (lean_obj_tag(x_333) == 0)
{
uint8_t x_334; 
x_334 = !lean_is_exclusive(x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_333, 0);
x_336 = lean_ctor_get(x_333, 1);
x_337 = l___private_Lean_Elab_App_19__elabAppLVals(x_335, x_2, x_3, x_4, x_5, x_6, x_8, x_336);
if (lean_obj_tag(x_337) == 0)
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_337);
if (x_338 == 0)
{
lean_object* x_339; 
x_339 = lean_array_push(x_7, x_337);
lean_ctor_set(x_333, 1, x_9);
lean_ctor_set(x_333, 0, x_339);
return x_333;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = lean_ctor_get(x_337, 0);
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_337);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
x_343 = lean_array_push(x_7, x_342);
lean_ctor_set(x_333, 1, x_9);
lean_ctor_set(x_333, 0, x_343);
return x_333;
}
}
else
{
lean_object* x_344; 
x_344 = lean_ctor_get(x_337, 0);
lean_inc(x_344);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
if (lean_obj_tag(x_345) == 0)
{
uint8_t x_346; 
lean_dec(x_344);
x_346 = !lean_is_exclusive(x_337);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_337, 0);
lean_dec(x_347);
x_348 = lean_ctor_get(x_345, 0);
lean_inc(x_348);
lean_dec(x_345);
lean_ctor_set(x_337, 0, x_348);
x_349 = lean_array_push(x_7, x_337);
lean_ctor_set(x_333, 1, x_9);
lean_ctor_set(x_333, 0, x_349);
return x_333;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_337, 1);
lean_inc(x_350);
lean_dec(x_337);
x_351 = lean_ctor_get(x_345, 0);
lean_inc(x_351);
lean_dec(x_345);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_350);
x_353 = lean_array_push(x_7, x_352);
lean_ctor_set(x_333, 1, x_9);
lean_ctor_set(x_333, 0, x_353);
return x_333;
}
}
else
{
uint8_t x_354; 
lean_free_object(x_333);
lean_dec(x_9);
lean_dec(x_7);
x_354 = !lean_is_exclusive(x_337);
if (x_354 == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_337, 0);
lean_dec(x_355);
return x_337;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_337, 1);
lean_inc(x_356);
lean_dec(x_337);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_344);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
else
{
uint8_t x_358; 
lean_free_object(x_333);
lean_dec(x_7);
x_358 = !lean_is_exclusive(x_337);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_337, 1);
lean_dec(x_359);
x_360 = lean_ctor_get(x_337, 0);
lean_dec(x_360);
lean_ctor_set(x_337, 1, x_9);
return x_337;
}
else
{
lean_object* x_361; 
lean_dec(x_337);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_344);
lean_ctor_set(x_361, 1, x_9);
return x_361;
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_333, 0);
x_363 = lean_ctor_get(x_333, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_333);
x_364 = l___private_Lean_Elab_App_19__elabAppLVals(x_362, x_2, x_3, x_4, x_5, x_6, x_8, x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_367 = x_364;
} else {
 lean_dec_ref(x_364);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
x_369 = lean_array_push(x_7, x_368);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_9);
return x_370;
}
else
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_364, 0);
lean_inc(x_371);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_371);
x_373 = lean_ctor_get(x_364, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_374 = x_364;
} else {
 lean_dec_ref(x_364);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_372, 0);
lean_inc(x_375);
lean_dec(x_372);
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_373);
x_377 = lean_array_push(x_7, x_376);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_9);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_9);
lean_dec(x_7);
x_379 = lean_ctor_get(x_364, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_380 = x_364;
} else {
 lean_dec_ref(x_364);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_371);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_7);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_382 = x_364;
} else {
 lean_dec_ref(x_364);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_371);
lean_ctor_set(x_383, 1, x_9);
return x_383;
}
}
}
}
else
{
lean_object* x_384; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_384 = lean_ctor_get(x_333, 0);
lean_inc(x_384);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
if (lean_obj_tag(x_385) == 0)
{
uint8_t x_386; 
lean_dec(x_384);
x_386 = !lean_is_exclusive(x_333);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_387 = lean_ctor_get(x_333, 0);
lean_dec(x_387);
x_388 = lean_ctor_get(x_385, 0);
lean_inc(x_388);
lean_dec(x_385);
lean_ctor_set(x_333, 0, x_388);
x_389 = lean_array_push(x_7, x_333);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_9);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_391 = lean_ctor_get(x_333, 1);
lean_inc(x_391);
lean_dec(x_333);
x_392 = lean_ctor_get(x_385, 0);
lean_inc(x_392);
lean_dec(x_385);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_391);
x_394 = lean_array_push(x_7, x_393);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_9);
return x_395;
}
}
else
{
uint8_t x_396; 
lean_dec(x_9);
lean_dec(x_7);
x_396 = !lean_is_exclusive(x_333);
if (x_396 == 0)
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_333, 0);
lean_dec(x_397);
return x_333;
}
else
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_333, 1);
lean_inc(x_398);
lean_dec(x_333);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_384);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
else
{
uint8_t x_400; 
lean_dec(x_7);
x_400 = !lean_is_exclusive(x_333);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_333, 1);
lean_dec(x_401);
x_402 = lean_ctor_get(x_333, 0);
lean_dec(x_402);
lean_ctor_set(x_333, 1, x_9);
return x_333;
}
else
{
lean_object* x_403; 
lean_dec(x_333);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_384);
lean_ctor_set(x_403, 1, x_9);
return x_403;
}
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_1);
x_404 = l_Lean_Syntax_getId(x_326);
lean_dec(x_326);
x_405 = l_Lean_Name_eraseMacroScopes(x_404);
lean_dec(x_404);
x_406 = l_Lean_Name_components(x_405);
x_407 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__1(x_406);
x_408 = l_List_append___rarg(x_407, x_2);
x_1 = x_324;
x_2 = x_408;
goto _start;
}
}
else
{
lean_object* x_410; lean_object* x_411; 
lean_dec(x_1);
x_410 = l_Lean_fieldIdxKind;
x_411 = l_Lean_Syntax_isNatLitAux(x_410, x_326);
lean_dec(x_326);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_412 = l_Nat_Inhabited;
x_413 = l_Option_get_x21___rarg___closed__3;
x_414 = lean_panic_fn(x_412, x_413);
x_415 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_415, 0, x_414);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_2);
x_1 = x_324;
x_2 = x_416;
goto _start;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_411, 0);
lean_inc(x_418);
lean_dec(x_411);
x_419 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_419, 0, x_418);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_2);
x_1 = x_324;
x_2 = x_420;
goto _start;
}
}
}
}
}
else
{
lean_object* x_430; uint8_t x_431; 
x_430 = l_Lean_Syntax_getArgs(x_1);
x_431 = !lean_is_exclusive(x_8);
if (x_431 == 0)
{
uint8_t x_432; lean_object* x_433; lean_object* x_434; 
x_432 = 0;
lean_ctor_set_uint8(x_8, sizeof(void*)*10 + 1, x_432);
x_433 = lean_unsigned_to_nat(0u);
x_434 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_430, x_433, x_7, x_8, x_9);
lean_dec(x_430);
lean_dec(x_1);
return x_434;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; uint8_t x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_435 = lean_ctor_get(x_8, 0);
x_436 = lean_ctor_get(x_8, 1);
x_437 = lean_ctor_get(x_8, 2);
x_438 = lean_ctor_get(x_8, 3);
x_439 = lean_ctor_get(x_8, 4);
x_440 = lean_ctor_get(x_8, 5);
x_441 = lean_ctor_get(x_8, 6);
x_442 = lean_ctor_get(x_8, 7);
x_443 = lean_ctor_get(x_8, 8);
x_444 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_445 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
x_446 = lean_ctor_get(x_8, 9);
lean_inc(x_446);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_8);
x_447 = 0;
x_448 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_448, 0, x_435);
lean_ctor_set(x_448, 1, x_436);
lean_ctor_set(x_448, 2, x_437);
lean_ctor_set(x_448, 3, x_438);
lean_ctor_set(x_448, 4, x_439);
lean_ctor_set(x_448, 5, x_440);
lean_ctor_set(x_448, 6, x_441);
lean_ctor_set(x_448, 7, x_442);
lean_ctor_set(x_448, 8, x_443);
lean_ctor_set(x_448, 9, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*10, x_444);
lean_ctor_set_uint8(x_448, sizeof(void*)*10 + 1, x_447);
lean_ctor_set_uint8(x_448, sizeof(void*)*10 + 2, x_445);
x_449 = lean_unsigned_to_nat(0u);
x_450 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_430, x_449, x_7, x_448, x_9);
lean_dec(x_430);
lean_dec(x_1);
return x_450;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l___private_Lean_Elab_App_21__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_21__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l___private_Lean_Elab_App_21__elabAppFn(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
return x_11;
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
lean_object* l_Lean_Elab_getRefPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_getRefPos___at_Lean_Elab_Term_throwError___spec__2(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = l_Lean_FileMap_toPosition(x_6, x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_Lean_FileMap_toPosition(x_10, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
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
lean_object* l___private_Lean_Elab_App_23__toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_getRefPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_Position_DecidableEq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = l_Nat_repr(x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Elab_App_23__toMessageData___closed__1;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Nat_repr(x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_4, 0, x_23);
return x_4;
}
else
{
lean_object* x_24; 
lean_dec(x_7);
x_24 = lean_ctor_get(x_1, 4);
lean_inc(x_24);
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_24);
return x_4;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = l_Lean_Position_DecidableEq(x_25, x_27);
lean_dec(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = l_Nat_repr(x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l___private_Lean_Elab_App_23__toMessageData___closed__1;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = l_Nat_repr(x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_ctor_get(x_1, 4);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_26);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_27);
x_45 = lean_ctor_get(x_1, 4);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_26);
return x_46;
}
}
}
}
lean_object* l_Lean_Elab_getRefPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getRefPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_23__toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_App_23__toMessageData(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_13 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_14 = l_unreachable_x21___rarg(x_13);
lean_inc(x_3);
x_15 = lean_apply_2(x_14, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_1, x_18);
x_20 = x_16;
x_21 = lean_array_fset(x_11, x_1, x_20);
lean_dec(x_1);
x_1 = x_19;
x_2 = x_21;
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
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
x_28 = l___private_Lean_Elab_App_23__toMessageData(x_27, x_3, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_1, x_31);
x_33 = x_29;
x_34 = lean_array_fset(x_11, x_1, x_33);
lean_dec(x_1);
x_1 = x_32;
x_2 = x_34;
x_4 = x_30;
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
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = x_1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
x_7 = x_6;
lean_inc(x_2);
x_8 = lean_apply_2(x_7, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MessageData_ofArray(x_9);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Term_throwError___rarg(x_13, x_2, x_10);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Lean_Elab_App_24__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_24__mergeFailures___rarg), 3, 0);
return x_2;
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
lean_object* l___private_Lean_Elab_App_25__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_box(0);
x_8 = 0;
x_9 = l_Array_empty___closed__1;
lean_inc(x_5);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_App_21__elabAppFn___main(x_1, x_7, x_2, x_3, x_4, x_8, x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_get_size(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_17 = l_Array_filterAux___main___at___private_Lean_Elab_App_22__getSuccess___spec__1(x_11, x_16, x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_eq(x_18, x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_14, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_5, 9);
x_23 = l_Lean_Elab_replaceRef(x_1, x_22);
lean_dec(x_22);
lean_dec(x_1);
lean_ctor_set(x_5, 9, x_23);
x_24 = l___private_Lean_Elab_App_24__mergeFailures___rarg(x_11, x_5, x_12);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
x_27 = lean_ctor_get(x_5, 2);
x_28 = lean_ctor_get(x_5, 3);
x_29 = lean_ctor_get(x_5, 4);
x_30 = lean_ctor_get(x_5, 5);
x_31 = lean_ctor_get(x_5, 6);
x_32 = lean_ctor_get(x_5, 7);
x_33 = lean_ctor_get(x_5, 8);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_37 = lean_ctor_get(x_5, 9);
lean_inc(x_37);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_38 = l_Lean_Elab_replaceRef(x_1, x_37);
lean_dec(x_37);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_27);
lean_ctor_set(x_39, 3, x_28);
lean_ctor_set(x_39, 4, x_29);
lean_ctor_set(x_39, 5, x_30);
lean_ctor_set(x_39, 6, x_31);
lean_ctor_set(x_39, 7, x_32);
lean_ctor_set(x_39, 8, x_33);
lean_ctor_set(x_39, 9, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*10, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*10 + 1, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*10 + 2, x_36);
x_40 = l___private_Lean_Elab_App_24__mergeFailures___rarg(x_11, x_39, x_12);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_11);
x_41 = l_Lean_Elab_Term_getLCtx(x_5, x_12);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Elab_Term_getOptions(x_5, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = x_17;
x_48 = l_Array_umapMAux___main___at___private_Lean_Elab_App_25__elabAppAux___spec__1(x_42, x_45, x_16, x_47);
x_49 = x_48;
x_50 = l_Lean_MessageData_ofArray(x_49);
lean_dec(x_49);
x_51 = l___private_Lean_Elab_App_25__elabAppAux___closed__3;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1, x_52, x_5, x_46);
lean_dec(x_1);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_1);
x_54 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_55 = lean_array_get(x_54, x_17, x_16);
lean_dec(x_17);
x_56 = l_Lean_Elab_Term_applyResult(x_55, x_5, x_12);
lean_dec(x_12);
lean_dec(x_5);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_1);
x_57 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get(x_57, x_11, x_58);
lean_dec(x_11);
x_60 = l_Lean_Elab_Term_applyResult(x_59, x_5, x_12);
lean_dec(x_12);
lean_dec(x_5);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_5);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_10);
if (x_61 == 0)
{
return x_10;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_10, 0);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_10);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
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
lean_dec(x_10);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_5);
x_29 = l_Lean_Elab_Term_addNamedArg(x_14, x_28, x_5, x_6);
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
lean_dec(x_10);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_5);
x_53 = l_Lean_Elab_Term_addNamedArg(x_37, x_52, x_5, x_6);
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
x_9 = l_Lean_importModules___closed__1;
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
x_12 = l___private_Lean_Elab_App_25__elabAppAux(x_9, x_10, x_11, x_2, x_3, x_8);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabApp___boxed), 4, 0);
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
x_6 = l___private_Lean_Elab_App_25__elabAppAux(x_1, x_5, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabIdent), 4, 0);
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
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNamedPattern), 4, 0);
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
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicitUniv), 4, 0);
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
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_72; uint8_t x_73; 
x_72 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_1);
x_73 = l_Lean_Syntax_isOfKind(x_1, x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = 0;
x_5 = x_74;
goto block_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = l_Lean_Syntax_getArgs(x_1);
x_76 = lean_array_get_size(x_75);
lean_dec(x_75);
x_77 = lean_unsigned_to_nat(2u);
x_78 = lean_nat_dec_eq(x_76, x_77);
lean_dec(x_76);
x_5 = x_78;
goto block_71;
}
block_71:
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
x_43 = l_Lean_identKind___closed__2;
lean_inc(x_8);
x_44 = l_Lean_Syntax_isOfKind(x_8, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_8);
x_46 = l_Lean_Syntax_isOfKind(x_8, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_1);
x_47 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
lean_inc(x_8);
x_48 = l_Lean_Syntax_isOfKind(x_8, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = 0;
x_9 = x_49;
goto block_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = l_Lean_Syntax_getArgs(x_8);
x_51 = lean_array_get_size(x_50);
lean_dec(x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
x_9 = x_53;
goto block_42;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = l_Lean_Syntax_getArgs(x_8);
x_55 = lean_array_get_size(x_54);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
lean_dec(x_1);
x_58 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
lean_inc(x_8);
x_59 = l_Lean_Syntax_isOfKind(x_8, x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_55);
x_60 = 0;
x_9 = x_60;
goto block_42;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_dec_eq(x_55, x_61);
lean_dec(x_55);
x_9 = x_62;
goto block_42;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_55);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Syntax_getArg(x_8, x_63);
x_65 = l_Lean_Syntax_isOfKind(x_64, x_43);
if (x_65 == 0)
{
uint8_t x_66; uint8_t x_67; lean_object* x_68; 
lean_dec(x_1);
x_66 = 1;
x_67 = 0;
x_68 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_66, x_67, x_8, x_3, x_4);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_8);
x_69 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_69;
}
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_8);
x_70 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_70;
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
x_3 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_App(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l___private_Lean_Elab_App_21__elabAppFn___main___closed__1 = _init_l___private_Lean_Elab_App_21__elabAppFn___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppFn___main___closed__1);
l___private_Lean_Elab_App_21__elabAppFn___main___closed__2 = _init_l___private_Lean_Elab_App_21__elabAppFn___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppFn___main___closed__2);
l___private_Lean_Elab_App_21__elabAppFn___main___closed__3 = _init_l___private_Lean_Elab_App_21__elabAppFn___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppFn___main___closed__3);
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
