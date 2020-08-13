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
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
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
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_getPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__6;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__7;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_App_23__toMessageData(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__8;
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
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
lean_object* l___private_Lean_Elab_App_23__toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__27;
lean_object* l___private_Lean_Elab_App_26__expandApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isTypeFormer(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__4;
lean_object* l___private_Lean_Elab_App_17__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabId(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
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
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawIdent(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__2;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__3;
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
extern lean_object* l_Lean_Format_repr___main___closed__13;
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__2;
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
lean_object* l_Lean_Elab_Term_elabId(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceInfo___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__7;
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__22;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAtom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_6__hasTypeMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__10;
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
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
extern lean_object* l_Lean_Syntax_inhabited;
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
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___regBuiltin_Lean_Elab_Term_elabId___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__10;
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__elabAppAux___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__20;
lean_object* l_Lean_Elab_Term_getCurrRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__2;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__getSuccess(lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__10;
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__2;
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
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_throwErrorAt___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___closed__1;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_22__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_1, x_5, x_6);
lean_dec(x_5);
lean_inc(x_2);
x_8 = lean_array_push(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_9);
x_12 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_9, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_registerSyntheticMVar(x_9, x_16, x_3, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_2 = x_11;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_9);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_2 = x_11;
x_4 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
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
x_61 = lean_ctor_get(x_3, 9);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
x_63 = lean_ctor_get_uint8(x_3, sizeof(void*)*11 + 1);
x_64 = lean_ctor_get(x_3, 10);
lean_inc(x_64);
x_65 = 0;
x_66 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_66, 0, x_52);
lean_ctor_set(x_66, 1, x_53);
lean_ctor_set(x_66, 2, x_54);
lean_ctor_set(x_66, 3, x_55);
lean_ctor_set(x_66, 4, x_56);
lean_ctor_set(x_66, 5, x_57);
lean_ctor_set(x_66, 6, x_58);
lean_ctor_set(x_66, 7, x_59);
lean_ctor_set(x_66, 8, x_60);
lean_ctor_set(x_66, 9, x_61);
lean_ctor_set(x_66, 10, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*11, x_62);
lean_ctor_set_uint8(x_66, sizeof(void*)*11 + 1, x_63);
lean_ctor_set_uint8(x_66, sizeof(void*)*11 + 2, x_65);
x_67 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_51, x_66, x_35);
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
x_37 = x_70;
x_38 = x_69;
goto block_50;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
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
x_86 = l_Lean_Elab_Term_throwError___rarg(x_85, x_3, x_72);
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
x_75 = l_Lean_Elab_Term_throwError___rarg(x_74, x_3, x_72);
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
uint8_t x_93; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_18);
if (x_93 == 0)
{
return x_18;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_18, 0);
x_95 = lean_ctor_get(x_18, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_18);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 10);
lean_dec(x_15);
lean_ctor_set(x_3, 10, x_7);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
x_21 = l___private_Lean_Elab_App_5__getForallBody___main(x_19, x_20, x_2);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_13);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Expr_hasLooseBVars(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l___private_Lean_Elab_App_6__hasTypeMVar(x_1, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_13);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l___private_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_24);
lean_dec(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_13);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_Elab_Term_isDefEq(x_13, x_24, x_3, x_4);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_13);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_4);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get(x_3, 3);
x_49 = lean_ctor_get(x_3, 4);
x_50 = lean_ctor_get(x_3, 5);
x_51 = lean_ctor_get(x_3, 6);
x_52 = lean_ctor_get(x_3, 7);
x_53 = lean_ctor_get(x_3, 8);
x_54 = lean_ctor_get(x_3, 9);
x_55 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
x_56 = lean_ctor_get_uint8(x_3, sizeof(void*)*11 + 1);
x_57 = lean_ctor_get_uint8(x_3, sizeof(void*)*11 + 2);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
x_58 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_47);
lean_ctor_set(x_58, 3, x_48);
lean_ctor_set(x_58, 4, x_49);
lean_ctor_set(x_58, 5, x_50);
lean_ctor_set(x_58, 6, x_51);
lean_ctor_set(x_58, 7, x_52);
lean_ctor_set(x_58, 8, x_53);
lean_ctor_set(x_58, 9, x_54);
lean_ctor_set(x_58, 10, x_7);
lean_ctor_set_uint8(x_58, sizeof(void*)*11, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*11 + 1, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*11 + 2, x_57);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_array_get_size(x_59);
lean_dec(x_59);
x_61 = lean_ctor_get(x_1, 3);
lean_inc(x_61);
x_62 = lean_nat_sub(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
x_63 = lean_ctor_get(x_1, 4);
lean_inc(x_63);
x_64 = l___private_Lean_Elab_App_5__getForallBody___main(x_62, x_63, x_2);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_58);
lean_dec(x_13);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_4);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l_Lean_Expr_hasLooseBVars(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = l___private_Lean_Elab_App_6__hasTypeMVar(x_1, x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_58);
lean_dec(x_13);
lean_dec(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_4);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = l___private_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_67);
lean_dec(x_1);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_67);
lean_dec(x_58);
lean_dec(x_13);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_4);
return x_74;
}
else
{
lean_object* x_75; 
x_75 = l_Lean_Elab_Term_isDefEq(x_13, x_67, x_58, x_4);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_67);
lean_dec(x_58);
lean_dec(x_13);
lean_dec(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_4);
return x_85;
}
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_4);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
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
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_16 = lean_ctor_get(x_4, 10);
lean_dec(x_16);
lean_inc(x_6);
lean_ctor_set(x_4, 10, x_6);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_whnfForall(x_3, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 7)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint64_t x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_18, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_18, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_18, 2);
lean_inc(x_97);
x_98 = lean_ctor_get_uint64(x_18, sizeof(void*)*3);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_95, x_11, x_99);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = (uint8_t)((x_98 << 24) >> 61);
switch (x_101) {
case 0:
{
uint8_t x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; uint8_t x_107; 
x_102 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_103 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_103, 0, x_6);
lean_ctor_set(x_103, 1, x_7);
lean_ctor_set(x_103, 2, x_8);
lean_ctor_set(x_103, 3, x_10);
lean_ctor_set(x_103, 4, x_11);
lean_ctor_set(x_103, 5, x_12);
lean_ctor_set(x_103, 6, x_13);
lean_ctor_set_uint8(x_103, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 1, x_102);
x_104 = lean_array_get_size(x_7);
x_105 = lean_nat_dec_lt(x_10, x_104);
lean_dec(x_104);
lean_inc(x_4);
lean_inc(x_1);
x_106 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_18, x_4, x_19);
x_107 = !lean_is_exclusive(x_1);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_1, 6);
lean_dec(x_108);
x_109 = lean_ctor_get(x_1, 5);
lean_dec(x_109);
x_110 = lean_ctor_get(x_1, 4);
lean_dec(x_110);
x_111 = lean_ctor_get(x_1, 3);
lean_dec(x_111);
x_112 = lean_ctor_get(x_1, 2);
lean_dec(x_112);
x_113 = lean_ctor_get(x_1, 1);
lean_dec(x_113);
x_114 = lean_ctor_get(x_1, 0);
lean_dec(x_114);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_106, 1);
lean_inc(x_115);
lean_dec(x_106);
if (x_105 == 0)
{
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_173; 
x_173 = l_Lean_Expr_getOptParamDefault_x3f(x_96);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
x_174 = l_Lean_Expr_getAutoParamTactic_x3f(x_96);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_175 = lean_box(0);
x_116 = x_175;
goto block_172;
}
else
{
lean_object* x_176; 
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
if (lean_obj_tag(x_176) == 4)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Lean_Elab_Term_getEnv___rarg(x_115);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_179, x_177);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_185 = l_Lean_Elab_Term_throwError___rarg(x_184, x_4, x_180);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
lean_dec(x_181);
x_187 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_180);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = l_Lean_Elab_Term_getMainModule___rarg(x_188);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = l_Lean_Syntax_getArgs(x_186);
lean_dec(x_186);
x_192 = l_Array_empty___closed__1;
x_193 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_191, x_191, x_99, x_192);
lean_dec(x_191);
x_194 = l_Lean_nullKind___closed__2;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_array_push(x_192, x_195);
x_197 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_200 = lean_array_push(x_199, x_198);
x_201 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_202 = lean_array_push(x_200, x_201);
x_203 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_206 = l_Lean_Expr_getAppNumArgsAux___main(x_96, x_99);
x_207 = lean_nat_sub(x_206, x_99);
lean_dec(x_206);
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_sub(x_207, x_208);
lean_dec(x_207);
x_210 = l_Lean_Expr_getRevArg_x21___main(x_96, x_209);
lean_dec(x_96);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_211, 0, x_204);
lean_inc(x_4);
lean_inc(x_2);
x_212 = l___private_Lean_Elab_App_2__elabArg(x_2, x_211, x_210, x_4, x_190);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
lean_inc(x_213);
x_215 = l_Lean_mkApp(x_2, x_213);
x_216 = lean_expr_instantiate1(x_97, x_213);
lean_dec(x_213);
lean_dec(x_97);
x_1 = x_103;
x_2 = x_215;
x_3 = x_216;
x_5 = x_214;
goto _start;
}
else
{
uint8_t x_218; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_218 = !lean_is_exclusive(x_212);
if (x_218 == 0)
{
return x_212;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_212, 0);
x_220 = lean_ctor_get(x_212, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_212);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_205, 0);
lean_inc(x_222);
lean_dec(x_205);
x_223 = l_Lean_Syntax_replaceInfo___main(x_222, x_204);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
lean_inc(x_4);
lean_inc(x_2);
x_225 = l___private_Lean_Elab_App_2__elabArg(x_2, x_224, x_210, x_4, x_190);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
lean_inc(x_226);
x_228 = l_Lean_mkApp(x_2, x_226);
x_229 = lean_expr_instantiate1(x_97, x_226);
lean_dec(x_226);
lean_dec(x_97);
x_1 = x_103;
x_2 = x_228;
x_3 = x_229;
x_5 = x_227;
goto _start;
}
else
{
uint8_t x_231; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_231 = !lean_is_exclusive(x_225);
if (x_231 == 0)
{
return x_225;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_225, 0);
x_233 = lean_ctor_get(x_225, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_225);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_176);
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_235 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_236 = l_Lean_Elab_Term_throwError___rarg(x_235, x_4, x_115);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_237 = lean_ctor_get(x_173, 0);
lean_inc(x_237);
lean_dec(x_173);
lean_inc(x_237);
x_238 = l_Lean_mkApp(x_2, x_237);
x_239 = lean_expr_instantiate1(x_97, x_237);
lean_dec(x_237);
lean_dec(x_97);
x_1 = x_103;
x_2 = x_238;
x_3 = x_239;
x_5 = x_115;
goto _start;
}
}
else
{
lean_object* x_241; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_241 = lean_box(0);
x_116 = x_241;
goto block_172;
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_103);
lean_dec(x_95);
lean_dec(x_3);
x_242 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_243 = l___private_Lean_Elab_App_2__elabArg(x_2, x_242, x_96, x_4, x_115);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_add(x_10, x_246);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_102);
lean_inc(x_244);
x_248 = l_Lean_mkApp(x_2, x_244);
x_249 = lean_expr_instantiate1(x_97, x_244);
lean_dec(x_244);
lean_dec(x_97);
x_2 = x_248;
x_3 = x_249;
x_5 = x_245;
goto _start;
}
else
{
uint8_t x_251; 
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_251 = !lean_is_exclusive(x_243);
if (x_251 == 0)
{
return x_243;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_243, 0);
x_253 = lean_ctor_get(x_243, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_243);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
block_172:
{
uint8_t x_117; 
lean_dec(x_116);
x_117 = l_Array_isEmpty___rarg(x_11);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_118, 0, x_95);
x_119 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_120 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_122 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = x_11;
x_124 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_123);
x_125 = x_124;
x_126 = l_Array_toList___rarg(x_125);
lean_dec(x_125);
x_127 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_126);
x_128 = l_Array_HasRepr___rarg___closed__1;
x_129 = lean_string_append(x_128, x_127);
lean_dec(x_127);
x_130 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_122);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_Elab_Term_throwError___rarg(x_132, x_4, x_115);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_95);
lean_dec(x_11);
x_161 = l_Lean_Elab_Term_getOptions(x_4, x_115);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lean_Elab_Term_getCurrRef(x_4, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_168 = l_Lean_checkTraceOption(x_162, x_167);
lean_dec(x_162);
if (x_168 == 0)
{
lean_dec(x_165);
x_134 = x_166;
goto block_160;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_inc(x_2);
x_169 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_169, 0, x_2);
lean_inc(x_4);
x_170 = l_Lean_Elab_Term_logTrace(x_167, x_165, x_169, x_4, x_166);
lean_dec(x_165);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_134 = x_171;
goto block_160;
}
block_160:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_135; 
lean_dec(x_3);
x_135 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_134);
lean_dec(x_12);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_2);
return x_135;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_2);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_135);
if (x_140 == 0)
{
return x_135;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_135, 0);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_135);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_8, 0);
lean_inc(x_144);
lean_dec(x_8);
lean_inc(x_4);
x_145 = l_Lean_Elab_Term_isDefEq(x_144, x_3, x_4, x_134);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_146);
lean_dec(x_12);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_147, 0);
lean_dec(x_149);
lean_ctor_set(x_147, 0, x_2);
return x_147;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_2);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
else
{
uint8_t x_152; 
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_147);
if (x_152 == 0)
{
return x_147;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_147, 0);
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_147);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_145);
if (x_156 == 0)
{
return x_145;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_145, 0);
x_158 = lean_ctor_get(x_145, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_145);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
}
}
else
{
uint8_t x_255; 
lean_free_object(x_1);
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_255 = !lean_is_exclusive(x_106);
if (x_255 == 0)
{
return x_106;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_106, 0);
x_257 = lean_ctor_get(x_106, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_106);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_106, 1);
lean_inc(x_259);
lean_dec(x_106);
if (x_105 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_315; 
x_315 = l_Lean_Expr_getOptParamDefault_x3f(x_96);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
x_316 = l_Lean_Expr_getAutoParamTactic_x3f(x_96);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_317 = lean_box(0);
x_260 = x_317;
goto block_314;
}
else
{
lean_object* x_318; 
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
lean_dec(x_316);
if (lean_obj_tag(x_318) == 4)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
lean_dec(x_318);
x_320 = l_Lean_Elab_Term_getEnv___rarg(x_259);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_321, x_319);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
lean_dec(x_323);
x_325 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = l_Lean_Elab_Term_throwError___rarg(x_326, x_4, x_322);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_328 = lean_ctor_get(x_323, 0);
lean_inc(x_328);
lean_dec(x_323);
x_329 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_322);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
x_331 = l_Lean_Elab_Term_getMainModule___rarg(x_330);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
lean_dec(x_331);
x_333 = l_Lean_Syntax_getArgs(x_328);
lean_dec(x_328);
x_334 = l_Array_empty___closed__1;
x_335 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_333, x_333, x_99, x_334);
lean_dec(x_333);
x_336 = l_Lean_nullKind___closed__2;
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_335);
x_338 = lean_array_push(x_334, x_337);
x_339 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
x_341 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_342 = lean_array_push(x_341, x_340);
x_343 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_344 = lean_array_push(x_342, x_343);
x_345 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_344);
x_347 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_348 = l_Lean_Expr_getAppNumArgsAux___main(x_96, x_99);
x_349 = lean_nat_sub(x_348, x_99);
lean_dec(x_348);
x_350 = lean_unsigned_to_nat(1u);
x_351 = lean_nat_sub(x_349, x_350);
lean_dec(x_349);
x_352 = l_Lean_Expr_getRevArg_x21___main(x_96, x_351);
lean_dec(x_96);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_346);
lean_inc(x_4);
lean_inc(x_2);
x_354 = l___private_Lean_Elab_App_2__elabArg(x_2, x_353, x_352, x_4, x_332);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
lean_inc(x_355);
x_357 = l_Lean_mkApp(x_2, x_355);
x_358 = lean_expr_instantiate1(x_97, x_355);
lean_dec(x_355);
lean_dec(x_97);
x_1 = x_103;
x_2 = x_357;
x_3 = x_358;
x_5 = x_356;
goto _start;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_360 = lean_ctor_get(x_354, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_354, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_362 = x_354;
} else {
 lean_dec_ref(x_354);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_347, 0);
lean_inc(x_364);
lean_dec(x_347);
x_365 = l_Lean_Syntax_replaceInfo___main(x_364, x_346);
x_366 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_366, 0, x_365);
lean_inc(x_4);
lean_inc(x_2);
x_367 = l___private_Lean_Elab_App_2__elabArg(x_2, x_366, x_352, x_4, x_332);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
lean_inc(x_368);
x_370 = l_Lean_mkApp(x_2, x_368);
x_371 = lean_expr_instantiate1(x_97, x_368);
lean_dec(x_368);
lean_dec(x_97);
x_1 = x_103;
x_2 = x_370;
x_3 = x_371;
x_5 = x_369;
goto _start;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_373 = lean_ctor_get(x_367, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_367, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_375 = x_367;
} else {
 lean_dec_ref(x_367);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
}
}
else
{
lean_object* x_377; lean_object* x_378; 
lean_dec(x_318);
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_377 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_378 = l_Lean_Elab_Term_throwError___rarg(x_377, x_4, x_259);
return x_378;
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_379 = lean_ctor_get(x_315, 0);
lean_inc(x_379);
lean_dec(x_315);
lean_inc(x_379);
x_380 = l_Lean_mkApp(x_2, x_379);
x_381 = lean_expr_instantiate1(x_97, x_379);
lean_dec(x_379);
lean_dec(x_97);
x_1 = x_103;
x_2 = x_380;
x_3 = x_381;
x_5 = x_259;
goto _start;
}
}
else
{
lean_object* x_383; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_383 = lean_box(0);
x_260 = x_383;
goto block_314;
}
}
else
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_103);
lean_dec(x_95);
lean_dec(x_3);
x_384 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_385 = l___private_Lean_Elab_App_2__elabArg(x_2, x_384, x_96, x_4, x_259);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = lean_unsigned_to_nat(1u);
x_389 = lean_nat_add(x_10, x_388);
lean_dec(x_10);
x_390 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_390, 0, x_6);
lean_ctor_set(x_390, 1, x_7);
lean_ctor_set(x_390, 2, x_8);
lean_ctor_set(x_390, 3, x_389);
lean_ctor_set(x_390, 4, x_11);
lean_ctor_set(x_390, 5, x_12);
lean_ctor_set(x_390, 6, x_13);
lean_ctor_set_uint8(x_390, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_390, sizeof(void*)*7 + 1, x_102);
lean_inc(x_386);
x_391 = l_Lean_mkApp(x_2, x_386);
x_392 = lean_expr_instantiate1(x_97, x_386);
lean_dec(x_386);
lean_dec(x_97);
x_1 = x_390;
x_2 = x_391;
x_3 = x_392;
x_5 = x_387;
goto _start;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_394 = lean_ctor_get(x_385, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_385, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_396 = x_385;
} else {
 lean_dec_ref(x_385);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
return x_397;
}
}
block_314:
{
uint8_t x_261; 
lean_dec(x_260);
x_261 = l_Array_isEmpty___rarg(x_11);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_262 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_262, 0, x_95);
x_263 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_264 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_262);
x_265 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_266 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = x_11;
x_268 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_267);
x_269 = x_268;
x_270 = l_Array_toList___rarg(x_269);
lean_dec(x_269);
x_271 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_270);
x_272 = l_Array_HasRepr___rarg___closed__1;
x_273 = lean_string_append(x_272, x_271);
lean_dec(x_271);
x_274 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_275, 0, x_274);
x_276 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_276, 0, x_266);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_Elab_Term_throwError___rarg(x_276, x_4, x_259);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
lean_dec(x_95);
lean_dec(x_11);
x_303 = l_Lean_Elab_Term_getOptions(x_4, x_259);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = l_Lean_Elab_Term_getCurrRef(x_4, x_305);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_310 = l_Lean_checkTraceOption(x_304, x_309);
lean_dec(x_304);
if (x_310 == 0)
{
lean_dec(x_307);
x_278 = x_308;
goto block_302;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_inc(x_2);
x_311 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_311, 0, x_2);
lean_inc(x_4);
x_312 = l_Lean_Elab_Term_logTrace(x_309, x_307, x_311, x_4, x_308);
lean_dec(x_307);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_278 = x_313;
goto block_302;
}
block_302:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_279; 
lean_dec(x_3);
x_279 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_278);
lean_dec(x_12);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_281 = x_279;
} else {
 lean_dec_ref(x_279);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_2);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_2);
x_283 = lean_ctor_get(x_279, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_279, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_285 = x_279;
} else {
 lean_dec_ref(x_279);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_8, 0);
lean_inc(x_287);
lean_dec(x_8);
lean_inc(x_4);
x_288 = l_Lean_Elab_Term_isDefEq(x_287, x_3, x_4, x_278);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
lean_dec(x_288);
x_290 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_289);
lean_dec(x_12);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_292 = x_290;
} else {
 lean_dec_ref(x_290);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_2);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_2);
x_294 = lean_ctor_get(x_290, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_290, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_296 = x_290;
} else {
 lean_dec_ref(x_290);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_298 = lean_ctor_get(x_288, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_288, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_300 = x_288;
} else {
 lean_dec_ref(x_288);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
}
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_398 = lean_ctor_get(x_106, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_106, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_400 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
case 1:
{
if (x_9 == 0)
{
uint8_t x_402; 
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_3);
x_402 = !lean_is_exclusive(x_1);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_1, 6);
lean_dec(x_403);
x_404 = lean_ctor_get(x_1, 5);
lean_dec(x_404);
x_405 = lean_ctor_get(x_1, 4);
lean_dec(x_405);
x_406 = lean_ctor_get(x_1, 3);
lean_dec(x_406);
x_407 = lean_ctor_get(x_1, 2);
lean_dec(x_407);
x_408 = lean_ctor_get(x_1, 1);
lean_dec(x_408);
x_409 = lean_ctor_get(x_1, 0);
lean_dec(x_409);
x_410 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_410, 0, x_96);
x_411 = 0;
x_412 = lean_box(0);
lean_inc(x_4);
x_413 = l_Lean_Elab_Term_mkFreshExprMVar(x_410, x_411, x_412, x_4, x_19);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
lean_inc(x_4);
lean_inc(x_414);
x_416 = l_Lean_Elab_Term_isTypeFormer(x_414, x_4, x_415);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; uint8_t x_418; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_unbox(x_417);
lean_dec(x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
lean_dec(x_416);
lean_inc(x_414);
x_420 = l_Lean_mkApp(x_2, x_414);
x_421 = lean_expr_instantiate1(x_97, x_414);
lean_dec(x_414);
lean_dec(x_97);
x_2 = x_420;
x_3 = x_421;
x_5 = x_419;
goto _start;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_423 = lean_ctor_get(x_416, 1);
lean_inc(x_423);
lean_dec(x_416);
x_424 = l_Lean_Expr_mvarId_x21(x_414);
x_425 = lean_array_push(x_13, x_424);
lean_ctor_set(x_1, 6, x_425);
lean_inc(x_414);
x_426 = l_Lean_mkApp(x_2, x_414);
x_427 = lean_expr_instantiate1(x_97, x_414);
lean_dec(x_414);
lean_dec(x_97);
x_2 = x_426;
x_3 = x_427;
x_5 = x_423;
goto _start;
}
}
else
{
uint8_t x_429; 
lean_dec(x_414);
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_429 = !lean_is_exclusive(x_416);
if (x_429 == 0)
{
return x_416;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_416, 0);
x_431 = lean_ctor_get(x_416, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_416);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
else
{
lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_1);
x_433 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_433, 0, x_96);
x_434 = 0;
x_435 = lean_box(0);
lean_inc(x_4);
x_436 = l_Lean_Elab_Term_mkFreshExprMVar(x_433, x_434, x_435, x_4, x_19);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
lean_inc(x_4);
lean_inc(x_437);
x_439 = l_Lean_Elab_Term_isTypeFormer(x_437, x_4, x_438);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; uint8_t x_441; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_unbox(x_440);
lean_dec(x_440);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_442 = lean_ctor_get(x_439, 1);
lean_inc(x_442);
lean_dec(x_439);
x_443 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_443, 0, x_6);
lean_ctor_set(x_443, 1, x_7);
lean_ctor_set(x_443, 2, x_8);
lean_ctor_set(x_443, 3, x_10);
lean_ctor_set(x_443, 4, x_11);
lean_ctor_set(x_443, 5, x_12);
lean_ctor_set(x_443, 6, x_13);
lean_ctor_set_uint8(x_443, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 1, x_15);
lean_inc(x_437);
x_444 = l_Lean_mkApp(x_2, x_437);
x_445 = lean_expr_instantiate1(x_97, x_437);
lean_dec(x_437);
lean_dec(x_97);
x_1 = x_443;
x_2 = x_444;
x_3 = x_445;
x_5 = x_442;
goto _start;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_447 = lean_ctor_get(x_439, 1);
lean_inc(x_447);
lean_dec(x_439);
x_448 = l_Lean_Expr_mvarId_x21(x_437);
x_449 = lean_array_push(x_13, x_448);
x_450 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_450, 0, x_6);
lean_ctor_set(x_450, 1, x_7);
lean_ctor_set(x_450, 2, x_8);
lean_ctor_set(x_450, 3, x_10);
lean_ctor_set(x_450, 4, x_11);
lean_ctor_set(x_450, 5, x_12);
lean_ctor_set(x_450, 6, x_449);
lean_ctor_set_uint8(x_450, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_450, sizeof(void*)*7 + 1, x_15);
lean_inc(x_437);
x_451 = l_Lean_mkApp(x_2, x_437);
x_452 = lean_expr_instantiate1(x_97, x_437);
lean_dec(x_437);
lean_dec(x_97);
x_1 = x_450;
x_2 = x_451;
x_3 = x_452;
x_5 = x_447;
goto _start;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_437);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_454 = lean_ctor_get(x_439, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_439, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_456 = x_439;
} else {
 lean_dec_ref(x_439);
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
}
else
{
lean_object* x_458; uint8_t x_459; lean_object* x_460; uint8_t x_461; 
x_458 = lean_array_get_size(x_7);
x_459 = lean_nat_dec_lt(x_10, x_458);
lean_dec(x_458);
lean_inc(x_4);
lean_inc(x_1);
x_460 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_18, x_4, x_19);
x_461 = !lean_is_exclusive(x_1);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_1, 6);
lean_dec(x_462);
x_463 = lean_ctor_get(x_1, 5);
lean_dec(x_463);
x_464 = lean_ctor_get(x_1, 4);
lean_dec(x_464);
x_465 = lean_ctor_get(x_1, 3);
lean_dec(x_465);
x_466 = lean_ctor_get(x_1, 2);
lean_dec(x_466);
x_467 = lean_ctor_get(x_1, 1);
lean_dec(x_467);
x_468 = lean_ctor_get(x_1, 0);
lean_dec(x_468);
if (lean_obj_tag(x_460) == 0)
{
if (x_459 == 0)
{
lean_object* x_469; uint8_t x_470; 
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_469 = lean_ctor_get(x_460, 1);
lean_inc(x_469);
lean_dec(x_460);
x_470 = l_Array_isEmpty___rarg(x_11);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_471 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_471, 0, x_95);
x_472 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_473 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_471);
x_474 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_475 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
x_476 = x_11;
x_477 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_476);
x_478 = x_477;
x_479 = l_Array_toList___rarg(x_478);
lean_dec(x_478);
x_480 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_479);
x_481 = l_Array_HasRepr___rarg___closed__1;
x_482 = lean_string_append(x_481, x_480);
lean_dec(x_480);
x_483 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_483, 0, x_482);
x_484 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_484, 0, x_483);
x_485 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_485, 0, x_475);
lean_ctor_set(x_485, 1, x_484);
x_486 = l_Lean_Elab_Term_throwError___rarg(x_485, x_4, x_469);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
lean_dec(x_95);
lean_dec(x_11);
x_514 = l_Lean_Elab_Term_getOptions(x_4, x_469);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
x_517 = l_Lean_Elab_Term_getCurrRef(x_4, x_516);
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
x_520 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_521 = l_Lean_checkTraceOption(x_515, x_520);
lean_dec(x_515);
if (x_521 == 0)
{
lean_dec(x_518);
x_487 = x_519;
goto block_513;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_inc(x_2);
x_522 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_522, 0, x_2);
lean_inc(x_4);
x_523 = l_Lean_Elab_Term_logTrace(x_520, x_518, x_522, x_4, x_519);
lean_dec(x_518);
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
lean_dec(x_523);
x_487 = x_524;
goto block_513;
}
block_513:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_488; 
lean_dec(x_3);
x_488 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_487);
lean_dec(x_12);
if (lean_obj_tag(x_488) == 0)
{
uint8_t x_489; 
x_489 = !lean_is_exclusive(x_488);
if (x_489 == 0)
{
lean_object* x_490; 
x_490 = lean_ctor_get(x_488, 0);
lean_dec(x_490);
lean_ctor_set(x_488, 0, x_2);
return x_488;
}
else
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_488, 1);
lean_inc(x_491);
lean_dec(x_488);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_2);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
else
{
uint8_t x_493; 
lean_dec(x_2);
x_493 = !lean_is_exclusive(x_488);
if (x_493 == 0)
{
return x_488;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_488, 0);
x_495 = lean_ctor_get(x_488, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_488);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
}
else
{
lean_object* x_497; lean_object* x_498; 
x_497 = lean_ctor_get(x_8, 0);
lean_inc(x_497);
lean_dec(x_8);
lean_inc(x_4);
x_498 = l_Lean_Elab_Term_isDefEq(x_497, x_3, x_4, x_487);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; 
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
lean_dec(x_498);
x_500 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_499);
lean_dec(x_12);
if (lean_obj_tag(x_500) == 0)
{
uint8_t x_501; 
x_501 = !lean_is_exclusive(x_500);
if (x_501 == 0)
{
lean_object* x_502; 
x_502 = lean_ctor_get(x_500, 0);
lean_dec(x_502);
lean_ctor_set(x_500, 0, x_2);
return x_500;
}
else
{
lean_object* x_503; lean_object* x_504; 
x_503 = lean_ctor_get(x_500, 1);
lean_inc(x_503);
lean_dec(x_500);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_2);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
else
{
uint8_t x_505; 
lean_dec(x_2);
x_505 = !lean_is_exclusive(x_500);
if (x_505 == 0)
{
return x_500;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_500, 0);
x_507 = lean_ctor_get(x_500, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_500);
x_508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
return x_508;
}
}
}
else
{
uint8_t x_509; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_509 = !lean_is_exclusive(x_498);
if (x_509 == 0)
{
return x_498;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_510 = lean_ctor_get(x_498, 0);
x_511 = lean_ctor_get(x_498, 1);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_498);
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
return x_512;
}
}
}
}
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_95);
lean_dec(x_3);
x_525 = lean_ctor_get(x_460, 1);
lean_inc(x_525);
lean_dec(x_460);
x_526 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_527 = l___private_Lean_Elab_App_2__elabArg(x_2, x_526, x_96, x_4, x_525);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; lean_object* x_534; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
x_530 = lean_unsigned_to_nat(1u);
x_531 = lean_nat_add(x_10, x_530);
lean_dec(x_10);
x_532 = 1;
lean_ctor_set(x_1, 3, x_531);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_532);
lean_inc(x_528);
x_533 = l_Lean_mkApp(x_2, x_528);
x_534 = lean_expr_instantiate1(x_97, x_528);
lean_dec(x_528);
lean_dec(x_97);
x_2 = x_533;
x_3 = x_534;
x_5 = x_529;
goto _start;
}
else
{
uint8_t x_536; 
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_536 = !lean_is_exclusive(x_527);
if (x_536 == 0)
{
return x_527;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_537 = lean_ctor_get(x_527, 0);
x_538 = lean_ctor_get(x_527, 1);
lean_inc(x_538);
lean_inc(x_537);
lean_dec(x_527);
x_539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
return x_539;
}
}
}
}
else
{
uint8_t x_540; 
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_540 = !lean_is_exclusive(x_460);
if (x_540 == 0)
{
return x_460;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_460, 0);
x_542 = lean_ctor_get(x_460, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_460);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_460) == 0)
{
if (x_459 == 0)
{
lean_object* x_544; uint8_t x_545; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_544 = lean_ctor_get(x_460, 1);
lean_inc(x_544);
lean_dec(x_460);
x_545 = l_Array_isEmpty___rarg(x_11);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_546 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_546, 0, x_95);
x_547 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_548 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_546);
x_549 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_550 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
x_551 = x_11;
x_552 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_551);
x_553 = x_552;
x_554 = l_Array_toList___rarg(x_553);
lean_dec(x_553);
x_555 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_554);
x_556 = l_Array_HasRepr___rarg___closed__1;
x_557 = lean_string_append(x_556, x_555);
lean_dec(x_555);
x_558 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_558, 0, x_557);
x_559 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_559, 0, x_558);
x_560 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_560, 0, x_550);
lean_ctor_set(x_560, 1, x_559);
x_561 = l_Lean_Elab_Term_throwError___rarg(x_560, x_4, x_544);
return x_561;
}
else
{
lean_object* x_562; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; 
lean_dec(x_95);
lean_dec(x_11);
x_587 = l_Lean_Elab_Term_getOptions(x_4, x_544);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
x_590 = l_Lean_Elab_Term_getCurrRef(x_4, x_589);
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_593 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_594 = l_Lean_checkTraceOption(x_588, x_593);
lean_dec(x_588);
if (x_594 == 0)
{
lean_dec(x_591);
x_562 = x_592;
goto block_586;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_inc(x_2);
x_595 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_595, 0, x_2);
lean_inc(x_4);
x_596 = l_Lean_Elab_Term_logTrace(x_593, x_591, x_595, x_4, x_592);
lean_dec(x_591);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
lean_dec(x_596);
x_562 = x_597;
goto block_586;
}
block_586:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_563; 
lean_dec(x_3);
x_563 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_562);
lean_dec(x_12);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_563, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 lean_ctor_release(x_563, 1);
 x_565 = x_563;
} else {
 lean_dec_ref(x_563);
 x_565 = lean_box(0);
}
if (lean_is_scalar(x_565)) {
 x_566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_566 = x_565;
}
lean_ctor_set(x_566, 0, x_2);
lean_ctor_set(x_566, 1, x_564);
return x_566;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec(x_2);
x_567 = lean_ctor_get(x_563, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_563, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 lean_ctor_release(x_563, 1);
 x_569 = x_563;
} else {
 lean_dec_ref(x_563);
 x_569 = lean_box(0);
}
if (lean_is_scalar(x_569)) {
 x_570 = lean_alloc_ctor(1, 2, 0);
} else {
 x_570 = x_569;
}
lean_ctor_set(x_570, 0, x_567);
lean_ctor_set(x_570, 1, x_568);
return x_570;
}
}
else
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_ctor_get(x_8, 0);
lean_inc(x_571);
lean_dec(x_8);
lean_inc(x_4);
x_572 = l_Lean_Elab_Term_isDefEq(x_571, x_3, x_4, x_562);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_ctor_get(x_572, 1);
lean_inc(x_573);
lean_dec(x_572);
x_574 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_573);
lean_dec(x_12);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_576 = x_574;
} else {
 lean_dec_ref(x_574);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_576)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_576;
}
lean_ctor_set(x_577, 0, x_2);
lean_ctor_set(x_577, 1, x_575);
return x_577;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_2);
x_578 = lean_ctor_get(x_574, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_574, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_580 = x_574;
} else {
 lean_dec_ref(x_574);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(1, 2, 0);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_578);
lean_ctor_set(x_581, 1, x_579);
return x_581;
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_582 = lean_ctor_get(x_572, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_572, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_584 = x_572;
} else {
 lean_dec_ref(x_572);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_582);
lean_ctor_set(x_585, 1, x_583);
return x_585;
}
}
}
}
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_95);
lean_dec(x_3);
x_598 = lean_ctor_get(x_460, 1);
lean_inc(x_598);
lean_dec(x_460);
x_599 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_600 = l___private_Lean_Elab_App_2__elabArg(x_2, x_599, x_96, x_4, x_598);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
x_603 = lean_unsigned_to_nat(1u);
x_604 = lean_nat_add(x_10, x_603);
lean_dec(x_10);
x_605 = 1;
x_606 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_606, 0, x_6);
lean_ctor_set(x_606, 1, x_7);
lean_ctor_set(x_606, 2, x_8);
lean_ctor_set(x_606, 3, x_604);
lean_ctor_set(x_606, 4, x_11);
lean_ctor_set(x_606, 5, x_12);
lean_ctor_set(x_606, 6, x_13);
lean_ctor_set_uint8(x_606, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_606, sizeof(void*)*7 + 1, x_605);
lean_inc(x_601);
x_607 = l_Lean_mkApp(x_2, x_601);
x_608 = lean_expr_instantiate1(x_97, x_601);
lean_dec(x_601);
lean_dec(x_97);
x_1 = x_606;
x_2 = x_607;
x_3 = x_608;
x_5 = x_602;
goto _start;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_610 = lean_ctor_get(x_600, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_600, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_612 = x_600;
} else {
 lean_dec_ref(x_600);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_614 = lean_ctor_get(x_460, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_460, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_616 = x_460;
} else {
 lean_dec_ref(x_460);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_614);
lean_ctor_set(x_617, 1, x_615);
return x_617;
}
}
}
}
case 2:
{
uint8_t x_618; lean_object* x_619; lean_object* x_620; uint8_t x_621; lean_object* x_622; uint8_t x_623; 
x_618 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_619 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_619, 0, x_6);
lean_ctor_set(x_619, 1, x_7);
lean_ctor_set(x_619, 2, x_8);
lean_ctor_set(x_619, 3, x_10);
lean_ctor_set(x_619, 4, x_11);
lean_ctor_set(x_619, 5, x_12);
lean_ctor_set(x_619, 6, x_13);
lean_ctor_set_uint8(x_619, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_619, sizeof(void*)*7 + 1, x_618);
x_620 = lean_array_get_size(x_7);
x_621 = lean_nat_dec_lt(x_10, x_620);
lean_dec(x_620);
lean_inc(x_4);
lean_inc(x_1);
x_622 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_18, x_4, x_19);
x_623 = !lean_is_exclusive(x_1);
if (x_623 == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_624 = lean_ctor_get(x_1, 6);
lean_dec(x_624);
x_625 = lean_ctor_get(x_1, 5);
lean_dec(x_625);
x_626 = lean_ctor_get(x_1, 4);
lean_dec(x_626);
x_627 = lean_ctor_get(x_1, 3);
lean_dec(x_627);
x_628 = lean_ctor_get(x_1, 2);
lean_dec(x_628);
x_629 = lean_ctor_get(x_1, 1);
lean_dec(x_629);
x_630 = lean_ctor_get(x_1, 0);
lean_dec(x_630);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_631; lean_object* x_632; 
x_631 = lean_ctor_get(x_622, 1);
lean_inc(x_631);
lean_dec(x_622);
if (x_621 == 0)
{
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_689; 
x_689 = l_Lean_Expr_getOptParamDefault_x3f(x_96);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; 
x_690 = l_Lean_Expr_getAutoParamTactic_x3f(x_96);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_691 = lean_box(0);
x_632 = x_691;
goto block_688;
}
else
{
lean_object* x_692; 
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_692 = lean_ctor_get(x_690, 0);
lean_inc(x_692);
lean_dec(x_690);
if (lean_obj_tag(x_692) == 4)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
lean_dec(x_692);
x_694 = l_Lean_Elab_Term_getEnv___rarg(x_631);
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec(x_694);
x_697 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_695, x_693);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
lean_dec(x_697);
x_699 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_699, 0, x_698);
x_700 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_700, 0, x_699);
x_701 = l_Lean_Elab_Term_throwError___rarg(x_700, x_4, x_696);
return x_701;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_702 = lean_ctor_get(x_697, 0);
lean_inc(x_702);
lean_dec(x_697);
x_703 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_696);
x_704 = lean_ctor_get(x_703, 1);
lean_inc(x_704);
lean_dec(x_703);
x_705 = l_Lean_Elab_Term_getMainModule___rarg(x_704);
x_706 = lean_ctor_get(x_705, 1);
lean_inc(x_706);
lean_dec(x_705);
x_707 = l_Lean_Syntax_getArgs(x_702);
lean_dec(x_702);
x_708 = l_Array_empty___closed__1;
x_709 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_707, x_707, x_99, x_708);
lean_dec(x_707);
x_710 = l_Lean_nullKind___closed__2;
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_710);
lean_ctor_set(x_711, 1, x_709);
x_712 = lean_array_push(x_708, x_711);
x_713 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_712);
x_715 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_716 = lean_array_push(x_715, x_714);
x_717 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_718 = lean_array_push(x_716, x_717);
x_719 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_718);
x_721 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_722 = l_Lean_Expr_getAppNumArgsAux___main(x_96, x_99);
x_723 = lean_nat_sub(x_722, x_99);
lean_dec(x_722);
x_724 = lean_unsigned_to_nat(1u);
x_725 = lean_nat_sub(x_723, x_724);
lean_dec(x_723);
x_726 = l_Lean_Expr_getRevArg_x21___main(x_96, x_725);
lean_dec(x_96);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_727; lean_object* x_728; 
x_727 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_727, 0, x_720);
lean_inc(x_4);
lean_inc(x_2);
x_728 = l___private_Lean_Elab_App_2__elabArg(x_2, x_727, x_726, x_4, x_706);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
lean_dec(x_728);
lean_inc(x_729);
x_731 = l_Lean_mkApp(x_2, x_729);
x_732 = lean_expr_instantiate1(x_97, x_729);
lean_dec(x_729);
lean_dec(x_97);
x_1 = x_619;
x_2 = x_731;
x_3 = x_732;
x_5 = x_730;
goto _start;
}
else
{
uint8_t x_734; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_734 = !lean_is_exclusive(x_728);
if (x_734 == 0)
{
return x_728;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_735 = lean_ctor_get(x_728, 0);
x_736 = lean_ctor_get(x_728, 1);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_728);
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_735);
lean_ctor_set(x_737, 1, x_736);
return x_737;
}
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
x_738 = lean_ctor_get(x_721, 0);
lean_inc(x_738);
lean_dec(x_721);
x_739 = l_Lean_Syntax_replaceInfo___main(x_738, x_720);
x_740 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_740, 0, x_739);
lean_inc(x_4);
lean_inc(x_2);
x_741 = l___private_Lean_Elab_App_2__elabArg(x_2, x_740, x_726, x_4, x_706);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
lean_inc(x_742);
x_744 = l_Lean_mkApp(x_2, x_742);
x_745 = lean_expr_instantiate1(x_97, x_742);
lean_dec(x_742);
lean_dec(x_97);
x_1 = x_619;
x_2 = x_744;
x_3 = x_745;
x_5 = x_743;
goto _start;
}
else
{
uint8_t x_747; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_747 = !lean_is_exclusive(x_741);
if (x_747 == 0)
{
return x_741;
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_748 = lean_ctor_get(x_741, 0);
x_749 = lean_ctor_get(x_741, 1);
lean_inc(x_749);
lean_inc(x_748);
lean_dec(x_741);
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_748);
lean_ctor_set(x_750, 1, x_749);
return x_750;
}
}
}
}
}
else
{
lean_object* x_751; lean_object* x_752; 
lean_dec(x_692);
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_751 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_752 = l_Lean_Elab_Term_throwError___rarg(x_751, x_4, x_631);
return x_752;
}
}
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_753 = lean_ctor_get(x_689, 0);
lean_inc(x_753);
lean_dec(x_689);
lean_inc(x_753);
x_754 = l_Lean_mkApp(x_2, x_753);
x_755 = lean_expr_instantiate1(x_97, x_753);
lean_dec(x_753);
lean_dec(x_97);
x_1 = x_619;
x_2 = x_754;
x_3 = x_755;
x_5 = x_631;
goto _start;
}
}
else
{
lean_object* x_757; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_757 = lean_box(0);
x_632 = x_757;
goto block_688;
}
}
else
{
lean_object* x_758; lean_object* x_759; 
lean_dec(x_619);
lean_dec(x_95);
lean_dec(x_3);
x_758 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_759 = l___private_Lean_Elab_App_2__elabArg(x_2, x_758, x_96, x_4, x_631);
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
lean_dec(x_759);
x_762 = lean_unsigned_to_nat(1u);
x_763 = lean_nat_add(x_10, x_762);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_763);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_618);
lean_inc(x_760);
x_764 = l_Lean_mkApp(x_2, x_760);
x_765 = lean_expr_instantiate1(x_97, x_760);
lean_dec(x_760);
lean_dec(x_97);
x_2 = x_764;
x_3 = x_765;
x_5 = x_761;
goto _start;
}
else
{
uint8_t x_767; 
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_767 = !lean_is_exclusive(x_759);
if (x_767 == 0)
{
return x_759;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_768 = lean_ctor_get(x_759, 0);
x_769 = lean_ctor_get(x_759, 1);
lean_inc(x_769);
lean_inc(x_768);
lean_dec(x_759);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
return x_770;
}
}
}
block_688:
{
uint8_t x_633; 
lean_dec(x_632);
x_633 = l_Array_isEmpty___rarg(x_11);
if (x_633 == 0)
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_634 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_634, 0, x_95);
x_635 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_636 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_634);
x_637 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_638 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
x_639 = x_11;
x_640 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_639);
x_641 = x_640;
x_642 = l_Array_toList___rarg(x_641);
lean_dec(x_641);
x_643 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_642);
x_644 = l_Array_HasRepr___rarg___closed__1;
x_645 = lean_string_append(x_644, x_643);
lean_dec(x_643);
x_646 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_646, 0, x_645);
x_647 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_647, 0, x_646);
x_648 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_648, 0, x_638);
lean_ctor_set(x_648, 1, x_647);
x_649 = l_Lean_Elab_Term_throwError___rarg(x_648, x_4, x_631);
return x_649;
}
else
{
lean_object* x_650; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; 
lean_dec(x_95);
lean_dec(x_11);
x_677 = l_Lean_Elab_Term_getOptions(x_4, x_631);
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_677, 1);
lean_inc(x_679);
lean_dec(x_677);
x_680 = l_Lean_Elab_Term_getCurrRef(x_4, x_679);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
x_683 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_684 = l_Lean_checkTraceOption(x_678, x_683);
lean_dec(x_678);
if (x_684 == 0)
{
lean_dec(x_681);
x_650 = x_682;
goto block_676;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
lean_inc(x_2);
x_685 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_685, 0, x_2);
lean_inc(x_4);
x_686 = l_Lean_Elab_Term_logTrace(x_683, x_681, x_685, x_4, x_682);
lean_dec(x_681);
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
lean_dec(x_686);
x_650 = x_687;
goto block_676;
}
block_676:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_651; 
lean_dec(x_3);
x_651 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_650);
lean_dec(x_12);
if (lean_obj_tag(x_651) == 0)
{
uint8_t x_652; 
x_652 = !lean_is_exclusive(x_651);
if (x_652 == 0)
{
lean_object* x_653; 
x_653 = lean_ctor_get(x_651, 0);
lean_dec(x_653);
lean_ctor_set(x_651, 0, x_2);
return x_651;
}
else
{
lean_object* x_654; lean_object* x_655; 
x_654 = lean_ctor_get(x_651, 1);
lean_inc(x_654);
lean_dec(x_651);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_2);
lean_ctor_set(x_655, 1, x_654);
return x_655;
}
}
else
{
uint8_t x_656; 
lean_dec(x_2);
x_656 = !lean_is_exclusive(x_651);
if (x_656 == 0)
{
return x_651;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_651, 0);
x_658 = lean_ctor_get(x_651, 1);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_651);
x_659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_659, 0, x_657);
lean_ctor_set(x_659, 1, x_658);
return x_659;
}
}
}
else
{
lean_object* x_660; lean_object* x_661; 
x_660 = lean_ctor_get(x_8, 0);
lean_inc(x_660);
lean_dec(x_8);
lean_inc(x_4);
x_661 = l_Lean_Elab_Term_isDefEq(x_660, x_3, x_4, x_650);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; 
x_662 = lean_ctor_get(x_661, 1);
lean_inc(x_662);
lean_dec(x_661);
x_663 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_662);
lean_dec(x_12);
if (lean_obj_tag(x_663) == 0)
{
uint8_t x_664; 
x_664 = !lean_is_exclusive(x_663);
if (x_664 == 0)
{
lean_object* x_665; 
x_665 = lean_ctor_get(x_663, 0);
lean_dec(x_665);
lean_ctor_set(x_663, 0, x_2);
return x_663;
}
else
{
lean_object* x_666; lean_object* x_667; 
x_666 = lean_ctor_get(x_663, 1);
lean_inc(x_666);
lean_dec(x_663);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_2);
lean_ctor_set(x_667, 1, x_666);
return x_667;
}
}
else
{
uint8_t x_668; 
lean_dec(x_2);
x_668 = !lean_is_exclusive(x_663);
if (x_668 == 0)
{
return x_663;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_663, 0);
x_670 = lean_ctor_get(x_663, 1);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_663);
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
return x_671;
}
}
}
else
{
uint8_t x_672; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_672 = !lean_is_exclusive(x_661);
if (x_672 == 0)
{
return x_661;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_661, 0);
x_674 = lean_ctor_get(x_661, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_661);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
}
}
}
}
else
{
uint8_t x_771; 
lean_free_object(x_1);
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_771 = !lean_is_exclusive(x_622);
if (x_771 == 0)
{
return x_622;
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_622, 0);
x_773 = lean_ctor_get(x_622, 1);
lean_inc(x_773);
lean_inc(x_772);
lean_dec(x_622);
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set(x_774, 1, x_773);
return x_774;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_775; lean_object* x_776; 
x_775 = lean_ctor_get(x_622, 1);
lean_inc(x_775);
lean_dec(x_622);
if (x_621 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_831; 
x_831 = l_Lean_Expr_getOptParamDefault_x3f(x_96);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; 
x_832 = l_Lean_Expr_getAutoParamTactic_x3f(x_96);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_833 = lean_box(0);
x_776 = x_833;
goto block_830;
}
else
{
lean_object* x_834; 
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_834 = lean_ctor_get(x_832, 0);
lean_inc(x_834);
lean_dec(x_832);
if (lean_obj_tag(x_834) == 4)
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
lean_dec(x_834);
x_836 = l_Lean_Elab_Term_getEnv___rarg(x_775);
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 1);
lean_inc(x_838);
lean_dec(x_836);
x_839 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_837, x_835);
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
lean_dec(x_839);
x_841 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_841, 0, x_840);
x_842 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_842, 0, x_841);
x_843 = l_Lean_Elab_Term_throwError___rarg(x_842, x_4, x_838);
return x_843;
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_844 = lean_ctor_get(x_839, 0);
lean_inc(x_844);
lean_dec(x_839);
x_845 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_838);
x_846 = lean_ctor_get(x_845, 1);
lean_inc(x_846);
lean_dec(x_845);
x_847 = l_Lean_Elab_Term_getMainModule___rarg(x_846);
x_848 = lean_ctor_get(x_847, 1);
lean_inc(x_848);
lean_dec(x_847);
x_849 = l_Lean_Syntax_getArgs(x_844);
lean_dec(x_844);
x_850 = l_Array_empty___closed__1;
x_851 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_849, x_849, x_99, x_850);
lean_dec(x_849);
x_852 = l_Lean_nullKind___closed__2;
x_853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_851);
x_854 = lean_array_push(x_850, x_853);
x_855 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_856 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_854);
x_857 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_858 = lean_array_push(x_857, x_856);
x_859 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_860 = lean_array_push(x_858, x_859);
x_861 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_862 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_860);
x_863 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_864 = l_Lean_Expr_getAppNumArgsAux___main(x_96, x_99);
x_865 = lean_nat_sub(x_864, x_99);
lean_dec(x_864);
x_866 = lean_unsigned_to_nat(1u);
x_867 = lean_nat_sub(x_865, x_866);
lean_dec(x_865);
x_868 = l_Lean_Expr_getRevArg_x21___main(x_96, x_867);
lean_dec(x_96);
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_869; lean_object* x_870; 
x_869 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_869, 0, x_862);
lean_inc(x_4);
lean_inc(x_2);
x_870 = l___private_Lean_Elab_App_2__elabArg(x_2, x_869, x_868, x_4, x_848);
if (lean_obj_tag(x_870) == 0)
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_870, 1);
lean_inc(x_872);
lean_dec(x_870);
lean_inc(x_871);
x_873 = l_Lean_mkApp(x_2, x_871);
x_874 = lean_expr_instantiate1(x_97, x_871);
lean_dec(x_871);
lean_dec(x_97);
x_1 = x_619;
x_2 = x_873;
x_3 = x_874;
x_5 = x_872;
goto _start;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_876 = lean_ctor_get(x_870, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_870, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_878 = x_870;
} else {
 lean_dec_ref(x_870);
 x_878 = lean_box(0);
}
if (lean_is_scalar(x_878)) {
 x_879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_879 = x_878;
}
lean_ctor_set(x_879, 0, x_876);
lean_ctor_set(x_879, 1, x_877);
return x_879;
}
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_880 = lean_ctor_get(x_863, 0);
lean_inc(x_880);
lean_dec(x_863);
x_881 = l_Lean_Syntax_replaceInfo___main(x_880, x_862);
x_882 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_882, 0, x_881);
lean_inc(x_4);
lean_inc(x_2);
x_883 = l___private_Lean_Elab_App_2__elabArg(x_2, x_882, x_868, x_4, x_848);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_883, 1);
lean_inc(x_885);
lean_dec(x_883);
lean_inc(x_884);
x_886 = l_Lean_mkApp(x_2, x_884);
x_887 = lean_expr_instantiate1(x_97, x_884);
lean_dec(x_884);
lean_dec(x_97);
x_1 = x_619;
x_2 = x_886;
x_3 = x_887;
x_5 = x_885;
goto _start;
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_889 = lean_ctor_get(x_883, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_883, 1);
lean_inc(x_890);
if (lean_is_exclusive(x_883)) {
 lean_ctor_release(x_883, 0);
 lean_ctor_release(x_883, 1);
 x_891 = x_883;
} else {
 lean_dec_ref(x_883);
 x_891 = lean_box(0);
}
if (lean_is_scalar(x_891)) {
 x_892 = lean_alloc_ctor(1, 2, 0);
} else {
 x_892 = x_891;
}
lean_ctor_set(x_892, 0, x_889);
lean_ctor_set(x_892, 1, x_890);
return x_892;
}
}
}
}
else
{
lean_object* x_893; lean_object* x_894; 
lean_dec(x_834);
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_893 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_894 = l_Lean_Elab_Term_throwError___rarg(x_893, x_4, x_775);
return x_894;
}
}
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_895 = lean_ctor_get(x_831, 0);
lean_inc(x_895);
lean_dec(x_831);
lean_inc(x_895);
x_896 = l_Lean_mkApp(x_2, x_895);
x_897 = lean_expr_instantiate1(x_97, x_895);
lean_dec(x_895);
lean_dec(x_97);
x_1 = x_619;
x_2 = x_896;
x_3 = x_897;
x_5 = x_775;
goto _start;
}
}
else
{
lean_object* x_899; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_899 = lean_box(0);
x_776 = x_899;
goto block_830;
}
}
else
{
lean_object* x_900; lean_object* x_901; 
lean_dec(x_619);
lean_dec(x_95);
lean_dec(x_3);
x_900 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_901 = l___private_Lean_Elab_App_2__elabArg(x_2, x_900, x_96, x_4, x_775);
if (lean_obj_tag(x_901) == 0)
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_901, 1);
lean_inc(x_903);
lean_dec(x_901);
x_904 = lean_unsigned_to_nat(1u);
x_905 = lean_nat_add(x_10, x_904);
lean_dec(x_10);
x_906 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_906, 0, x_6);
lean_ctor_set(x_906, 1, x_7);
lean_ctor_set(x_906, 2, x_8);
lean_ctor_set(x_906, 3, x_905);
lean_ctor_set(x_906, 4, x_11);
lean_ctor_set(x_906, 5, x_12);
lean_ctor_set(x_906, 6, x_13);
lean_ctor_set_uint8(x_906, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_906, sizeof(void*)*7 + 1, x_618);
lean_inc(x_902);
x_907 = l_Lean_mkApp(x_2, x_902);
x_908 = lean_expr_instantiate1(x_97, x_902);
lean_dec(x_902);
lean_dec(x_97);
x_1 = x_906;
x_2 = x_907;
x_3 = x_908;
x_5 = x_903;
goto _start;
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_910 = lean_ctor_get(x_901, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_901, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_912 = x_901;
} else {
 lean_dec_ref(x_901);
 x_912 = lean_box(0);
}
if (lean_is_scalar(x_912)) {
 x_913 = lean_alloc_ctor(1, 2, 0);
} else {
 x_913 = x_912;
}
lean_ctor_set(x_913, 0, x_910);
lean_ctor_set(x_913, 1, x_911);
return x_913;
}
}
block_830:
{
uint8_t x_777; 
lean_dec(x_776);
x_777 = l_Array_isEmpty___rarg(x_11);
if (x_777 == 0)
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_778 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_778, 0, x_95);
x_779 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_780 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_780, 0, x_779);
lean_ctor_set(x_780, 1, x_778);
x_781 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_782 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
x_783 = x_11;
x_784 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_783);
x_785 = x_784;
x_786 = l_Array_toList___rarg(x_785);
lean_dec(x_785);
x_787 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_786);
x_788 = l_Array_HasRepr___rarg___closed__1;
x_789 = lean_string_append(x_788, x_787);
lean_dec(x_787);
x_790 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_790, 0, x_789);
x_791 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_791, 0, x_790);
x_792 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_792, 0, x_782);
lean_ctor_set(x_792, 1, x_791);
x_793 = l_Lean_Elab_Term_throwError___rarg(x_792, x_4, x_775);
return x_793;
}
else
{
lean_object* x_794; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; uint8_t x_826; 
lean_dec(x_95);
lean_dec(x_11);
x_819 = l_Lean_Elab_Term_getOptions(x_4, x_775);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
lean_dec(x_819);
x_822 = l_Lean_Elab_Term_getCurrRef(x_4, x_821);
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec(x_822);
x_825 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_826 = l_Lean_checkTraceOption(x_820, x_825);
lean_dec(x_820);
if (x_826 == 0)
{
lean_dec(x_823);
x_794 = x_824;
goto block_818;
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; 
lean_inc(x_2);
x_827 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_827, 0, x_2);
lean_inc(x_4);
x_828 = l_Lean_Elab_Term_logTrace(x_825, x_823, x_827, x_4, x_824);
lean_dec(x_823);
x_829 = lean_ctor_get(x_828, 1);
lean_inc(x_829);
lean_dec(x_828);
x_794 = x_829;
goto block_818;
}
block_818:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_795; 
lean_dec(x_3);
x_795 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_794);
lean_dec(x_12);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_796 = lean_ctor_get(x_795, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 lean_ctor_release(x_795, 1);
 x_797 = x_795;
} else {
 lean_dec_ref(x_795);
 x_797 = lean_box(0);
}
if (lean_is_scalar(x_797)) {
 x_798 = lean_alloc_ctor(0, 2, 0);
} else {
 x_798 = x_797;
}
lean_ctor_set(x_798, 0, x_2);
lean_ctor_set(x_798, 1, x_796);
return x_798;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_2);
x_799 = lean_ctor_get(x_795, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_795, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 lean_ctor_release(x_795, 1);
 x_801 = x_795;
} else {
 lean_dec_ref(x_795);
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
else
{
lean_object* x_803; lean_object* x_804; 
x_803 = lean_ctor_get(x_8, 0);
lean_inc(x_803);
lean_dec(x_8);
lean_inc(x_4);
x_804 = l_Lean_Elab_Term_isDefEq(x_803, x_3, x_4, x_794);
if (lean_obj_tag(x_804) == 0)
{
lean_object* x_805; lean_object* x_806; 
x_805 = lean_ctor_get(x_804, 1);
lean_inc(x_805);
lean_dec(x_804);
x_806 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_805);
lean_dec(x_12);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_807 = lean_ctor_get(x_806, 1);
lean_inc(x_807);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_808 = x_806;
} else {
 lean_dec_ref(x_806);
 x_808 = lean_box(0);
}
if (lean_is_scalar(x_808)) {
 x_809 = lean_alloc_ctor(0, 2, 0);
} else {
 x_809 = x_808;
}
lean_ctor_set(x_809, 0, x_2);
lean_ctor_set(x_809, 1, x_807);
return x_809;
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_dec(x_2);
x_810 = lean_ctor_get(x_806, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_806, 1);
lean_inc(x_811);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_812 = x_806;
} else {
 lean_dec_ref(x_806);
 x_812 = lean_box(0);
}
if (lean_is_scalar(x_812)) {
 x_813 = lean_alloc_ctor(1, 2, 0);
} else {
 x_813 = x_812;
}
lean_ctor_set(x_813, 0, x_810);
lean_ctor_set(x_813, 1, x_811);
return x_813;
}
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_814 = lean_ctor_get(x_804, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_804, 1);
lean_inc(x_815);
if (lean_is_exclusive(x_804)) {
 lean_ctor_release(x_804, 0);
 lean_ctor_release(x_804, 1);
 x_816 = x_804;
} else {
 lean_dec_ref(x_804);
 x_816 = lean_box(0);
}
if (lean_is_scalar(x_816)) {
 x_817 = lean_alloc_ctor(1, 2, 0);
} else {
 x_817 = x_816;
}
lean_ctor_set(x_817, 0, x_814);
lean_ctor_set(x_817, 1, x_815);
return x_817;
}
}
}
}
}
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
lean_dec(x_619);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_914 = lean_ctor_get(x_622, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_622, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_916 = x_622;
} else {
 lean_dec_ref(x_622);
 x_916 = lean_box(0);
}
if (lean_is_scalar(x_916)) {
 x_917 = lean_alloc_ctor(1, 2, 0);
} else {
 x_917 = x_916;
}
lean_ctor_set(x_917, 0, x_914);
lean_ctor_set(x_917, 1, x_915);
return x_917;
}
}
}
case 3:
{
if (x_9 == 0)
{
uint8_t x_918; 
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_3);
x_918 = !lean_is_exclusive(x_1);
if (x_918 == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; uint8_t x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_919 = lean_ctor_get(x_1, 6);
lean_dec(x_919);
x_920 = lean_ctor_get(x_1, 5);
lean_dec(x_920);
x_921 = lean_ctor_get(x_1, 4);
lean_dec(x_921);
x_922 = lean_ctor_get(x_1, 3);
lean_dec(x_922);
x_923 = lean_ctor_get(x_1, 2);
lean_dec(x_923);
x_924 = lean_ctor_get(x_1, 1);
lean_dec(x_924);
x_925 = lean_ctor_get(x_1, 0);
lean_dec(x_925);
x_926 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_926, 0, x_96);
x_927 = 1;
x_928 = lean_box(0);
lean_inc(x_4);
x_929 = l_Lean_Elab_Term_mkFreshExprMVar(x_926, x_927, x_928, x_4, x_19);
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_929, 1);
lean_inc(x_931);
lean_dec(x_929);
x_932 = l_Lean_Expr_mvarId_x21(x_930);
x_933 = lean_array_push(x_12, x_932);
lean_ctor_set(x_1, 5, x_933);
lean_inc(x_930);
x_934 = l_Lean_mkApp(x_2, x_930);
x_935 = lean_expr_instantiate1(x_97, x_930);
lean_dec(x_930);
lean_dec(x_97);
x_2 = x_934;
x_3 = x_935;
x_5 = x_931;
goto _start;
}
else
{
lean_object* x_937; uint8_t x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
lean_dec(x_1);
x_937 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_937, 0, x_96);
x_938 = 1;
x_939 = lean_box(0);
lean_inc(x_4);
x_940 = l_Lean_Elab_Term_mkFreshExprMVar(x_937, x_938, x_939, x_4, x_19);
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_940, 1);
lean_inc(x_942);
lean_dec(x_940);
x_943 = l_Lean_Expr_mvarId_x21(x_941);
x_944 = lean_array_push(x_12, x_943);
x_945 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_945, 0, x_6);
lean_ctor_set(x_945, 1, x_7);
lean_ctor_set(x_945, 2, x_8);
lean_ctor_set(x_945, 3, x_10);
lean_ctor_set(x_945, 4, x_11);
lean_ctor_set(x_945, 5, x_944);
lean_ctor_set(x_945, 6, x_13);
lean_ctor_set_uint8(x_945, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_945, sizeof(void*)*7 + 1, x_15);
lean_inc(x_941);
x_946 = l_Lean_mkApp(x_2, x_941);
x_947 = lean_expr_instantiate1(x_97, x_941);
lean_dec(x_941);
lean_dec(x_97);
x_1 = x_945;
x_2 = x_946;
x_3 = x_947;
x_5 = x_942;
goto _start;
}
}
else
{
uint8_t x_949; 
x_949 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_949 == 0)
{
lean_object* x_950; uint8_t x_951; lean_object* x_952; uint8_t x_953; 
x_950 = lean_array_get_size(x_7);
x_951 = lean_nat_dec_lt(x_10, x_950);
lean_dec(x_950);
lean_inc(x_4);
lean_inc(x_1);
x_952 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_18, x_4, x_19);
x_953 = !lean_is_exclusive(x_1);
if (x_953 == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_954 = lean_ctor_get(x_1, 6);
lean_dec(x_954);
x_955 = lean_ctor_get(x_1, 5);
lean_dec(x_955);
x_956 = lean_ctor_get(x_1, 4);
lean_dec(x_956);
x_957 = lean_ctor_get(x_1, 3);
lean_dec(x_957);
x_958 = lean_ctor_get(x_1, 2);
lean_dec(x_958);
x_959 = lean_ctor_get(x_1, 1);
lean_dec(x_959);
x_960 = lean_ctor_get(x_1, 0);
lean_dec(x_960);
if (lean_obj_tag(x_952) == 0)
{
if (x_951 == 0)
{
lean_object* x_961; uint8_t x_962; 
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_961 = lean_ctor_get(x_952, 1);
lean_inc(x_961);
lean_dec(x_952);
x_962 = l_Array_isEmpty___rarg(x_11);
if (x_962 == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_963 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_963, 0, x_95);
x_964 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_965 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_965, 0, x_964);
lean_ctor_set(x_965, 1, x_963);
x_966 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_967 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_967, 0, x_965);
lean_ctor_set(x_967, 1, x_966);
x_968 = x_11;
x_969 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_968);
x_970 = x_969;
x_971 = l_Array_toList___rarg(x_970);
lean_dec(x_970);
x_972 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_971);
x_973 = l_Array_HasRepr___rarg___closed__1;
x_974 = lean_string_append(x_973, x_972);
lean_dec(x_972);
x_975 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_975, 0, x_974);
x_976 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_976, 0, x_975);
x_977 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_977, 0, x_967);
lean_ctor_set(x_977, 1, x_976);
x_978 = l_Lean_Elab_Term_throwError___rarg(x_977, x_4, x_961);
return x_978;
}
else
{
lean_object* x_979; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; uint8_t x_1013; 
lean_dec(x_95);
lean_dec(x_11);
x_1006 = l_Lean_Elab_Term_getOptions(x_4, x_961);
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1006, 1);
lean_inc(x_1008);
lean_dec(x_1006);
x_1009 = l_Lean_Elab_Term_getCurrRef(x_4, x_1008);
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
lean_dec(x_1009);
x_1012 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1013 = l_Lean_checkTraceOption(x_1007, x_1012);
lean_dec(x_1007);
if (x_1013 == 0)
{
lean_dec(x_1010);
x_979 = x_1011;
goto block_1005;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
lean_inc(x_2);
x_1014 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1014, 0, x_2);
lean_inc(x_4);
x_1015 = l_Lean_Elab_Term_logTrace(x_1012, x_1010, x_1014, x_4, x_1011);
lean_dec(x_1010);
x_1016 = lean_ctor_get(x_1015, 1);
lean_inc(x_1016);
lean_dec(x_1015);
x_979 = x_1016;
goto block_1005;
}
block_1005:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_980; 
lean_dec(x_3);
x_980 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_979);
lean_dec(x_12);
if (lean_obj_tag(x_980) == 0)
{
uint8_t x_981; 
x_981 = !lean_is_exclusive(x_980);
if (x_981 == 0)
{
lean_object* x_982; 
x_982 = lean_ctor_get(x_980, 0);
lean_dec(x_982);
lean_ctor_set(x_980, 0, x_2);
return x_980;
}
else
{
lean_object* x_983; lean_object* x_984; 
x_983 = lean_ctor_get(x_980, 1);
lean_inc(x_983);
lean_dec(x_980);
x_984 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_984, 0, x_2);
lean_ctor_set(x_984, 1, x_983);
return x_984;
}
}
else
{
uint8_t x_985; 
lean_dec(x_2);
x_985 = !lean_is_exclusive(x_980);
if (x_985 == 0)
{
return x_980;
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; 
x_986 = lean_ctor_get(x_980, 0);
x_987 = lean_ctor_get(x_980, 1);
lean_inc(x_987);
lean_inc(x_986);
lean_dec(x_980);
x_988 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_988, 0, x_986);
lean_ctor_set(x_988, 1, x_987);
return x_988;
}
}
}
else
{
lean_object* x_989; lean_object* x_990; 
x_989 = lean_ctor_get(x_8, 0);
lean_inc(x_989);
lean_dec(x_8);
lean_inc(x_4);
x_990 = l_Lean_Elab_Term_isDefEq(x_989, x_3, x_4, x_979);
if (lean_obj_tag(x_990) == 0)
{
lean_object* x_991; lean_object* x_992; 
x_991 = lean_ctor_get(x_990, 1);
lean_inc(x_991);
lean_dec(x_990);
x_992 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_991);
lean_dec(x_12);
if (lean_obj_tag(x_992) == 0)
{
uint8_t x_993; 
x_993 = !lean_is_exclusive(x_992);
if (x_993 == 0)
{
lean_object* x_994; 
x_994 = lean_ctor_get(x_992, 0);
lean_dec(x_994);
lean_ctor_set(x_992, 0, x_2);
return x_992;
}
else
{
lean_object* x_995; lean_object* x_996; 
x_995 = lean_ctor_get(x_992, 1);
lean_inc(x_995);
lean_dec(x_992);
x_996 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_996, 0, x_2);
lean_ctor_set(x_996, 1, x_995);
return x_996;
}
}
else
{
uint8_t x_997; 
lean_dec(x_2);
x_997 = !lean_is_exclusive(x_992);
if (x_997 == 0)
{
return x_992;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_998 = lean_ctor_get(x_992, 0);
x_999 = lean_ctor_get(x_992, 1);
lean_inc(x_999);
lean_inc(x_998);
lean_dec(x_992);
x_1000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set(x_1000, 1, x_999);
return x_1000;
}
}
}
else
{
uint8_t x_1001; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_1001 = !lean_is_exclusive(x_990);
if (x_1001 == 0)
{
return x_990;
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1002 = lean_ctor_get(x_990, 0);
x_1003 = lean_ctor_get(x_990, 1);
lean_inc(x_1003);
lean_inc(x_1002);
lean_dec(x_990);
x_1004 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1004, 0, x_1002);
lean_ctor_set(x_1004, 1, x_1003);
return x_1004;
}
}
}
}
}
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
lean_dec(x_95);
lean_dec(x_3);
x_1017 = lean_ctor_get(x_952, 1);
lean_inc(x_1017);
lean_dec(x_952);
x_1018 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_1019 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1018, x_96, x_4, x_1017);
if (lean_obj_tag(x_1019) == 0)
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; uint8_t x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1020 = lean_ctor_get(x_1019, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1019, 1);
lean_inc(x_1021);
lean_dec(x_1019);
x_1022 = lean_unsigned_to_nat(1u);
x_1023 = lean_nat_add(x_10, x_1022);
lean_dec(x_10);
x_1024 = 1;
lean_ctor_set(x_1, 3, x_1023);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_1024);
lean_inc(x_1020);
x_1025 = l_Lean_mkApp(x_2, x_1020);
x_1026 = lean_expr_instantiate1(x_97, x_1020);
lean_dec(x_1020);
lean_dec(x_97);
x_2 = x_1025;
x_3 = x_1026;
x_5 = x_1021;
goto _start;
}
else
{
uint8_t x_1028; 
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1028 = !lean_is_exclusive(x_1019);
if (x_1028 == 0)
{
return x_1019;
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1029 = lean_ctor_get(x_1019, 0);
x_1030 = lean_ctor_get(x_1019, 1);
lean_inc(x_1030);
lean_inc(x_1029);
lean_dec(x_1019);
x_1031 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1031, 0, x_1029);
lean_ctor_set(x_1031, 1, x_1030);
return x_1031;
}
}
}
}
else
{
uint8_t x_1032; 
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_1032 = !lean_is_exclusive(x_952);
if (x_1032 == 0)
{
return x_952;
}
else
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1033 = lean_ctor_get(x_952, 0);
x_1034 = lean_ctor_get(x_952, 1);
lean_inc(x_1034);
lean_inc(x_1033);
lean_dec(x_952);
x_1035 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1035, 0, x_1033);
lean_ctor_set(x_1035, 1, x_1034);
return x_1035;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_952) == 0)
{
if (x_951 == 0)
{
lean_object* x_1036; uint8_t x_1037; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_1036 = lean_ctor_get(x_952, 1);
lean_inc(x_1036);
lean_dec(x_952);
x_1037 = l_Array_isEmpty___rarg(x_11);
if (x_1037 == 0)
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1038 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1038, 0, x_95);
x_1039 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1040 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1040, 0, x_1039);
lean_ctor_set(x_1040, 1, x_1038);
x_1041 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1042 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1042, 0, x_1040);
lean_ctor_set(x_1042, 1, x_1041);
x_1043 = x_11;
x_1044 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_1043);
x_1045 = x_1044;
x_1046 = l_Array_toList___rarg(x_1045);
lean_dec(x_1045);
x_1047 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1046);
x_1048 = l_Array_HasRepr___rarg___closed__1;
x_1049 = lean_string_append(x_1048, x_1047);
lean_dec(x_1047);
x_1050 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1050, 0, x_1049);
x_1051 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1051, 0, x_1050);
x_1052 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1052, 0, x_1042);
lean_ctor_set(x_1052, 1, x_1051);
x_1053 = l_Lean_Elab_Term_throwError___rarg(x_1052, x_4, x_1036);
return x_1053;
}
else
{
lean_object* x_1054; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; uint8_t x_1086; 
lean_dec(x_95);
lean_dec(x_11);
x_1079 = l_Lean_Elab_Term_getOptions(x_4, x_1036);
x_1080 = lean_ctor_get(x_1079, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1079, 1);
lean_inc(x_1081);
lean_dec(x_1079);
x_1082 = l_Lean_Elab_Term_getCurrRef(x_4, x_1081);
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1082, 1);
lean_inc(x_1084);
lean_dec(x_1082);
x_1085 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1086 = l_Lean_checkTraceOption(x_1080, x_1085);
lean_dec(x_1080);
if (x_1086 == 0)
{
lean_dec(x_1083);
x_1054 = x_1084;
goto block_1078;
}
else
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
lean_inc(x_2);
x_1087 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1087, 0, x_2);
lean_inc(x_4);
x_1088 = l_Lean_Elab_Term_logTrace(x_1085, x_1083, x_1087, x_4, x_1084);
lean_dec(x_1083);
x_1089 = lean_ctor_get(x_1088, 1);
lean_inc(x_1089);
lean_dec(x_1088);
x_1054 = x_1089;
goto block_1078;
}
block_1078:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1055; 
lean_dec(x_3);
x_1055 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_1054);
lean_dec(x_12);
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
x_1056 = lean_ctor_get(x_1055, 1);
lean_inc(x_1056);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 lean_ctor_release(x_1055, 1);
 x_1057 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1057 = lean_box(0);
}
if (lean_is_scalar(x_1057)) {
 x_1058 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1058 = x_1057;
}
lean_ctor_set(x_1058, 0, x_2);
lean_ctor_set(x_1058, 1, x_1056);
return x_1058;
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
lean_dec(x_2);
x_1059 = lean_ctor_get(x_1055, 0);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1055, 1);
lean_inc(x_1060);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 lean_ctor_release(x_1055, 1);
 x_1061 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1061 = lean_box(0);
}
if (lean_is_scalar(x_1061)) {
 x_1062 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1062 = x_1061;
}
lean_ctor_set(x_1062, 0, x_1059);
lean_ctor_set(x_1062, 1, x_1060);
return x_1062;
}
}
else
{
lean_object* x_1063; lean_object* x_1064; 
x_1063 = lean_ctor_get(x_8, 0);
lean_inc(x_1063);
lean_dec(x_8);
lean_inc(x_4);
x_1064 = l_Lean_Elab_Term_isDefEq(x_1063, x_3, x_4, x_1054);
if (lean_obj_tag(x_1064) == 0)
{
lean_object* x_1065; lean_object* x_1066; 
x_1065 = lean_ctor_get(x_1064, 1);
lean_inc(x_1065);
lean_dec(x_1064);
x_1066 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_1065);
lean_dec(x_12);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1067 = lean_ctor_get(x_1066, 1);
lean_inc(x_1067);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1068 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1068 = lean_box(0);
}
if (lean_is_scalar(x_1068)) {
 x_1069 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1069 = x_1068;
}
lean_ctor_set(x_1069, 0, x_2);
lean_ctor_set(x_1069, 1, x_1067);
return x_1069;
}
else
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
lean_dec(x_2);
x_1070 = lean_ctor_get(x_1066, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1066, 1);
lean_inc(x_1071);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1072 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1072 = lean_box(0);
}
if (lean_is_scalar(x_1072)) {
 x_1073 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1073 = x_1072;
}
lean_ctor_set(x_1073, 0, x_1070);
lean_ctor_set(x_1073, 1, x_1071);
return x_1073;
}
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_1074 = lean_ctor_get(x_1064, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1064, 1);
lean_inc(x_1075);
if (lean_is_exclusive(x_1064)) {
 lean_ctor_release(x_1064, 0);
 lean_ctor_release(x_1064, 1);
 x_1076 = x_1064;
} else {
 lean_dec_ref(x_1064);
 x_1076 = lean_box(0);
}
if (lean_is_scalar(x_1076)) {
 x_1077 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1077 = x_1076;
}
lean_ctor_set(x_1077, 0, x_1074);
lean_ctor_set(x_1077, 1, x_1075);
return x_1077;
}
}
}
}
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_95);
lean_dec(x_3);
x_1090 = lean_ctor_get(x_952, 1);
lean_inc(x_1090);
lean_dec(x_952);
x_1091 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_1092 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1091, x_96, x_4, x_1090);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; uint8_t x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1092, 1);
lean_inc(x_1094);
lean_dec(x_1092);
x_1095 = lean_unsigned_to_nat(1u);
x_1096 = lean_nat_add(x_10, x_1095);
lean_dec(x_10);
x_1097 = 1;
x_1098 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1098, 0, x_6);
lean_ctor_set(x_1098, 1, x_7);
lean_ctor_set(x_1098, 2, x_8);
lean_ctor_set(x_1098, 3, x_1096);
lean_ctor_set(x_1098, 4, x_11);
lean_ctor_set(x_1098, 5, x_12);
lean_ctor_set(x_1098, 6, x_13);
lean_ctor_set_uint8(x_1098, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1098, sizeof(void*)*7 + 1, x_1097);
lean_inc(x_1093);
x_1099 = l_Lean_mkApp(x_2, x_1093);
x_1100 = lean_expr_instantiate1(x_97, x_1093);
lean_dec(x_1093);
lean_dec(x_97);
x_1 = x_1098;
x_2 = x_1099;
x_3 = x_1100;
x_5 = x_1094;
goto _start;
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1102 = lean_ctor_get(x_1092, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1092, 1);
lean_inc(x_1103);
if (lean_is_exclusive(x_1092)) {
 lean_ctor_release(x_1092, 0);
 lean_ctor_release(x_1092, 1);
 x_1104 = x_1092;
} else {
 lean_dec_ref(x_1092);
 x_1104 = lean_box(0);
}
if (lean_is_scalar(x_1104)) {
 x_1105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1105 = x_1104;
}
lean_ctor_set(x_1105, 0, x_1102);
lean_ctor_set(x_1105, 1, x_1103);
return x_1105;
}
}
}
else
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_1106 = lean_ctor_get(x_952, 0);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_952, 1);
lean_inc(x_1107);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_1108 = x_952;
} else {
 lean_dec_ref(x_952);
 x_1108 = lean_box(0);
}
if (lean_is_scalar(x_1108)) {
 x_1109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1109 = x_1108;
}
lean_ctor_set(x_1109, 0, x_1106);
lean_ctor_set(x_1109, 1, x_1107);
return x_1109;
}
}
}
else
{
uint8_t x_1110; 
lean_dec(x_95);
lean_dec(x_18);
lean_dec(x_3);
x_1110 = !lean_is_exclusive(x_1);
if (x_1110 == 0)
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; uint8_t x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1111 = lean_ctor_get(x_1, 6);
lean_dec(x_1111);
x_1112 = lean_ctor_get(x_1, 5);
lean_dec(x_1112);
x_1113 = lean_ctor_get(x_1, 4);
lean_dec(x_1113);
x_1114 = lean_ctor_get(x_1, 3);
lean_dec(x_1114);
x_1115 = lean_ctor_get(x_1, 2);
lean_dec(x_1115);
x_1116 = lean_ctor_get(x_1, 1);
lean_dec(x_1116);
x_1117 = lean_ctor_get(x_1, 0);
lean_dec(x_1117);
x_1118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1118, 0, x_96);
x_1119 = 1;
x_1120 = lean_box(0);
lean_inc(x_4);
x_1121 = l_Lean_Elab_Term_mkFreshExprMVar(x_1118, x_1119, x_1120, x_4, x_19);
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_1121, 1);
lean_inc(x_1123);
lean_dec(x_1121);
x_1124 = lean_unsigned_to_nat(1u);
x_1125 = lean_nat_add(x_10, x_1124);
lean_dec(x_10);
x_1126 = l_Lean_Expr_mvarId_x21(x_1122);
x_1127 = lean_array_push(x_12, x_1126);
lean_ctor_set(x_1, 5, x_1127);
lean_ctor_set(x_1, 3, x_1125);
lean_inc(x_1122);
x_1128 = l_Lean_mkApp(x_2, x_1122);
x_1129 = lean_expr_instantiate1(x_97, x_1122);
lean_dec(x_1122);
lean_dec(x_97);
x_2 = x_1128;
x_3 = x_1129;
x_5 = x_1123;
goto _start;
}
else
{
lean_object* x_1131; uint8_t x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
lean_dec(x_1);
x_1131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1131, 0, x_96);
x_1132 = 1;
x_1133 = lean_box(0);
lean_inc(x_4);
x_1134 = l_Lean_Elab_Term_mkFreshExprMVar(x_1131, x_1132, x_1133, x_4, x_19);
x_1135 = lean_ctor_get(x_1134, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1134, 1);
lean_inc(x_1136);
lean_dec(x_1134);
x_1137 = lean_unsigned_to_nat(1u);
x_1138 = lean_nat_add(x_10, x_1137);
lean_dec(x_10);
x_1139 = l_Lean_Expr_mvarId_x21(x_1135);
x_1140 = lean_array_push(x_12, x_1139);
x_1141 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1141, 0, x_6);
lean_ctor_set(x_1141, 1, x_7);
lean_ctor_set(x_1141, 2, x_8);
lean_ctor_set(x_1141, 3, x_1138);
lean_ctor_set(x_1141, 4, x_11);
lean_ctor_set(x_1141, 5, x_1140);
lean_ctor_set(x_1141, 6, x_13);
lean_ctor_set_uint8(x_1141, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1141, sizeof(void*)*7 + 1, x_15);
lean_inc(x_1135);
x_1142 = l_Lean_mkApp(x_2, x_1135);
x_1143 = lean_expr_instantiate1(x_97, x_1135);
lean_dec(x_1135);
lean_dec(x_97);
x_1 = x_1141;
x_2 = x_1142;
x_3 = x_1143;
x_5 = x_1136;
goto _start;
}
}
}
}
default: 
{
uint8_t x_1145; lean_object* x_1146; lean_object* x_1147; uint8_t x_1148; lean_object* x_1149; uint8_t x_1150; 
x_1145 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1146 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1146, 0, x_6);
lean_ctor_set(x_1146, 1, x_7);
lean_ctor_set(x_1146, 2, x_8);
lean_ctor_set(x_1146, 3, x_10);
lean_ctor_set(x_1146, 4, x_11);
lean_ctor_set(x_1146, 5, x_12);
lean_ctor_set(x_1146, 6, x_13);
lean_ctor_set_uint8(x_1146, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1146, sizeof(void*)*7 + 1, x_1145);
x_1147 = lean_array_get_size(x_7);
x_1148 = lean_nat_dec_lt(x_10, x_1147);
lean_dec(x_1147);
lean_inc(x_4);
lean_inc(x_1);
x_1149 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_18, x_4, x_19);
x_1150 = !lean_is_exclusive(x_1);
if (x_1150 == 0)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
x_1151 = lean_ctor_get(x_1, 6);
lean_dec(x_1151);
x_1152 = lean_ctor_get(x_1, 5);
lean_dec(x_1152);
x_1153 = lean_ctor_get(x_1, 4);
lean_dec(x_1153);
x_1154 = lean_ctor_get(x_1, 3);
lean_dec(x_1154);
x_1155 = lean_ctor_get(x_1, 2);
lean_dec(x_1155);
x_1156 = lean_ctor_get(x_1, 1);
lean_dec(x_1156);
x_1157 = lean_ctor_get(x_1, 0);
lean_dec(x_1157);
if (lean_obj_tag(x_1149) == 0)
{
lean_object* x_1158; lean_object* x_1159; 
x_1158 = lean_ctor_get(x_1149, 1);
lean_inc(x_1158);
lean_dec(x_1149);
if (x_1148 == 0)
{
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1216; 
x_1216 = l_Lean_Expr_getOptParamDefault_x3f(x_96);
if (lean_obj_tag(x_1216) == 0)
{
lean_object* x_1217; 
x_1217 = l_Lean_Expr_getAutoParamTactic_x3f(x_96);
if (lean_obj_tag(x_1217) == 0)
{
lean_object* x_1218; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_1218 = lean_box(0);
x_1159 = x_1218;
goto block_1215;
}
else
{
lean_object* x_1219; 
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1219 = lean_ctor_get(x_1217, 0);
lean_inc(x_1219);
lean_dec(x_1217);
if (lean_obj_tag(x_1219) == 4)
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1220 = lean_ctor_get(x_1219, 0);
lean_inc(x_1220);
lean_dec(x_1219);
x_1221 = l_Lean_Elab_Term_getEnv___rarg(x_1158);
x_1222 = lean_ctor_get(x_1221, 0);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1221, 1);
lean_inc(x_1223);
lean_dec(x_1221);
x_1224 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1222, x_1220);
if (lean_obj_tag(x_1224) == 0)
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_1225 = lean_ctor_get(x_1224, 0);
lean_inc(x_1225);
lean_dec(x_1224);
x_1226 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1226, 0, x_1225);
x_1227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1227, 0, x_1226);
x_1228 = l_Lean_Elab_Term_throwError___rarg(x_1227, x_4, x_1223);
return x_1228;
}
else
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
x_1229 = lean_ctor_get(x_1224, 0);
lean_inc(x_1229);
lean_dec(x_1224);
x_1230 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1223);
x_1231 = lean_ctor_get(x_1230, 1);
lean_inc(x_1231);
lean_dec(x_1230);
x_1232 = l_Lean_Elab_Term_getMainModule___rarg(x_1231);
x_1233 = lean_ctor_get(x_1232, 1);
lean_inc(x_1233);
lean_dec(x_1232);
x_1234 = l_Lean_Syntax_getArgs(x_1229);
lean_dec(x_1229);
x_1235 = l_Array_empty___closed__1;
x_1236 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1234, x_1234, x_99, x_1235);
lean_dec(x_1234);
x_1237 = l_Lean_nullKind___closed__2;
x_1238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1238, 0, x_1237);
lean_ctor_set(x_1238, 1, x_1236);
x_1239 = lean_array_push(x_1235, x_1238);
x_1240 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_1241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1241, 0, x_1240);
lean_ctor_set(x_1241, 1, x_1239);
x_1242 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1243 = lean_array_push(x_1242, x_1241);
x_1244 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1245 = lean_array_push(x_1243, x_1244);
x_1246 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1247, 0, x_1246);
lean_ctor_set(x_1247, 1, x_1245);
x_1248 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_1249 = l_Lean_Expr_getAppNumArgsAux___main(x_96, x_99);
x_1250 = lean_nat_sub(x_1249, x_99);
lean_dec(x_1249);
x_1251 = lean_unsigned_to_nat(1u);
x_1252 = lean_nat_sub(x_1250, x_1251);
lean_dec(x_1250);
x_1253 = l_Lean_Expr_getRevArg_x21___main(x_96, x_1252);
lean_dec(x_96);
if (lean_obj_tag(x_1248) == 0)
{
lean_object* x_1254; lean_object* x_1255; 
x_1254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1254, 0, x_1247);
lean_inc(x_4);
lean_inc(x_2);
x_1255 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1254, x_1253, x_4, x_1233);
if (lean_obj_tag(x_1255) == 0)
{
lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
x_1256 = lean_ctor_get(x_1255, 0);
lean_inc(x_1256);
x_1257 = lean_ctor_get(x_1255, 1);
lean_inc(x_1257);
lean_dec(x_1255);
lean_inc(x_1256);
x_1258 = l_Lean_mkApp(x_2, x_1256);
x_1259 = lean_expr_instantiate1(x_97, x_1256);
lean_dec(x_1256);
lean_dec(x_97);
x_1 = x_1146;
x_2 = x_1258;
x_3 = x_1259;
x_5 = x_1257;
goto _start;
}
else
{
uint8_t x_1261; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_1261 = !lean_is_exclusive(x_1255);
if (x_1261 == 0)
{
return x_1255;
}
else
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1262 = lean_ctor_get(x_1255, 0);
x_1263 = lean_ctor_get(x_1255, 1);
lean_inc(x_1263);
lean_inc(x_1262);
lean_dec(x_1255);
x_1264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1264, 0, x_1262);
lean_ctor_set(x_1264, 1, x_1263);
return x_1264;
}
}
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
x_1265 = lean_ctor_get(x_1248, 0);
lean_inc(x_1265);
lean_dec(x_1248);
x_1266 = l_Lean_Syntax_replaceInfo___main(x_1265, x_1247);
x_1267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1267, 0, x_1266);
lean_inc(x_4);
lean_inc(x_2);
x_1268 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1267, x_1253, x_4, x_1233);
if (lean_obj_tag(x_1268) == 0)
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1269 = lean_ctor_get(x_1268, 0);
lean_inc(x_1269);
x_1270 = lean_ctor_get(x_1268, 1);
lean_inc(x_1270);
lean_dec(x_1268);
lean_inc(x_1269);
x_1271 = l_Lean_mkApp(x_2, x_1269);
x_1272 = lean_expr_instantiate1(x_97, x_1269);
lean_dec(x_1269);
lean_dec(x_97);
x_1 = x_1146;
x_2 = x_1271;
x_3 = x_1272;
x_5 = x_1270;
goto _start;
}
else
{
uint8_t x_1274; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_1274 = !lean_is_exclusive(x_1268);
if (x_1274 == 0)
{
return x_1268;
}
else
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
x_1275 = lean_ctor_get(x_1268, 0);
x_1276 = lean_ctor_get(x_1268, 1);
lean_inc(x_1276);
lean_inc(x_1275);
lean_dec(x_1268);
x_1277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1277, 0, x_1275);
lean_ctor_set(x_1277, 1, x_1276);
return x_1277;
}
}
}
}
}
else
{
lean_object* x_1278; lean_object* x_1279; 
lean_dec(x_1219);
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_1278 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1279 = l_Lean_Elab_Term_throwError___rarg(x_1278, x_4, x_1158);
return x_1279;
}
}
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1280 = lean_ctor_get(x_1216, 0);
lean_inc(x_1280);
lean_dec(x_1216);
lean_inc(x_1280);
x_1281 = l_Lean_mkApp(x_2, x_1280);
x_1282 = lean_expr_instantiate1(x_97, x_1280);
lean_dec(x_1280);
lean_dec(x_97);
x_1 = x_1146;
x_2 = x_1281;
x_3 = x_1282;
x_5 = x_1158;
goto _start;
}
}
else
{
lean_object* x_1284; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_1284 = lean_box(0);
x_1159 = x_1284;
goto block_1215;
}
}
else
{
lean_object* x_1285; lean_object* x_1286; 
lean_dec(x_1146);
lean_dec(x_95);
lean_dec(x_3);
x_1285 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_1286 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1285, x_96, x_4, x_1158);
if (lean_obj_tag(x_1286) == 0)
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
x_1287 = lean_ctor_get(x_1286, 0);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1286, 1);
lean_inc(x_1288);
lean_dec(x_1286);
x_1289 = lean_unsigned_to_nat(1u);
x_1290 = lean_nat_add(x_10, x_1289);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_1290);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_1145);
lean_inc(x_1287);
x_1291 = l_Lean_mkApp(x_2, x_1287);
x_1292 = lean_expr_instantiate1(x_97, x_1287);
lean_dec(x_1287);
lean_dec(x_97);
x_2 = x_1291;
x_3 = x_1292;
x_5 = x_1288;
goto _start;
}
else
{
uint8_t x_1294; 
lean_free_object(x_1);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1294 = !lean_is_exclusive(x_1286);
if (x_1294 == 0)
{
return x_1286;
}
else
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1295 = lean_ctor_get(x_1286, 0);
x_1296 = lean_ctor_get(x_1286, 1);
lean_inc(x_1296);
lean_inc(x_1295);
lean_dec(x_1286);
x_1297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1297, 0, x_1295);
lean_ctor_set(x_1297, 1, x_1296);
return x_1297;
}
}
}
block_1215:
{
uint8_t x_1160; 
lean_dec(x_1159);
x_1160 = l_Array_isEmpty___rarg(x_11);
if (x_1160 == 0)
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1161 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1161, 0, x_95);
x_1162 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1163 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1163, 0, x_1162);
lean_ctor_set(x_1163, 1, x_1161);
x_1164 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1165 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1165, 0, x_1163);
lean_ctor_set(x_1165, 1, x_1164);
x_1166 = x_11;
x_1167 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_1166);
x_1168 = x_1167;
x_1169 = l_Array_toList___rarg(x_1168);
lean_dec(x_1168);
x_1170 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1169);
x_1171 = l_Array_HasRepr___rarg___closed__1;
x_1172 = lean_string_append(x_1171, x_1170);
lean_dec(x_1170);
x_1173 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1173, 0, x_1172);
x_1174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1174, 0, x_1173);
x_1175 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1175, 0, x_1165);
lean_ctor_set(x_1175, 1, x_1174);
x_1176 = l_Lean_Elab_Term_throwError___rarg(x_1175, x_4, x_1158);
return x_1176;
}
else
{
lean_object* x_1177; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; uint8_t x_1211; 
lean_dec(x_95);
lean_dec(x_11);
x_1204 = l_Lean_Elab_Term_getOptions(x_4, x_1158);
x_1205 = lean_ctor_get(x_1204, 0);
lean_inc(x_1205);
x_1206 = lean_ctor_get(x_1204, 1);
lean_inc(x_1206);
lean_dec(x_1204);
x_1207 = l_Lean_Elab_Term_getCurrRef(x_4, x_1206);
x_1208 = lean_ctor_get(x_1207, 0);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_1207, 1);
lean_inc(x_1209);
lean_dec(x_1207);
x_1210 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1211 = l_Lean_checkTraceOption(x_1205, x_1210);
lean_dec(x_1205);
if (x_1211 == 0)
{
lean_dec(x_1208);
x_1177 = x_1209;
goto block_1203;
}
else
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
lean_inc(x_2);
x_1212 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1212, 0, x_2);
lean_inc(x_4);
x_1213 = l_Lean_Elab_Term_logTrace(x_1210, x_1208, x_1212, x_4, x_1209);
lean_dec(x_1208);
x_1214 = lean_ctor_get(x_1213, 1);
lean_inc(x_1214);
lean_dec(x_1213);
x_1177 = x_1214;
goto block_1203;
}
block_1203:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1178; 
lean_dec(x_3);
x_1178 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_1177);
lean_dec(x_12);
if (lean_obj_tag(x_1178) == 0)
{
uint8_t x_1179; 
x_1179 = !lean_is_exclusive(x_1178);
if (x_1179 == 0)
{
lean_object* x_1180; 
x_1180 = lean_ctor_get(x_1178, 0);
lean_dec(x_1180);
lean_ctor_set(x_1178, 0, x_2);
return x_1178;
}
else
{
lean_object* x_1181; lean_object* x_1182; 
x_1181 = lean_ctor_get(x_1178, 1);
lean_inc(x_1181);
lean_dec(x_1178);
x_1182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1182, 0, x_2);
lean_ctor_set(x_1182, 1, x_1181);
return x_1182;
}
}
else
{
uint8_t x_1183; 
lean_dec(x_2);
x_1183 = !lean_is_exclusive(x_1178);
if (x_1183 == 0)
{
return x_1178;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1178, 0);
x_1185 = lean_ctor_get(x_1178, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1178);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
}
else
{
lean_object* x_1187; lean_object* x_1188; 
x_1187 = lean_ctor_get(x_8, 0);
lean_inc(x_1187);
lean_dec(x_8);
lean_inc(x_4);
x_1188 = l_Lean_Elab_Term_isDefEq(x_1187, x_3, x_4, x_1177);
if (lean_obj_tag(x_1188) == 0)
{
lean_object* x_1189; lean_object* x_1190; 
x_1189 = lean_ctor_get(x_1188, 1);
lean_inc(x_1189);
lean_dec(x_1188);
x_1190 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_1189);
lean_dec(x_12);
if (lean_obj_tag(x_1190) == 0)
{
uint8_t x_1191; 
x_1191 = !lean_is_exclusive(x_1190);
if (x_1191 == 0)
{
lean_object* x_1192; 
x_1192 = lean_ctor_get(x_1190, 0);
lean_dec(x_1192);
lean_ctor_set(x_1190, 0, x_2);
return x_1190;
}
else
{
lean_object* x_1193; lean_object* x_1194; 
x_1193 = lean_ctor_get(x_1190, 1);
lean_inc(x_1193);
lean_dec(x_1190);
x_1194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1194, 0, x_2);
lean_ctor_set(x_1194, 1, x_1193);
return x_1194;
}
}
else
{
uint8_t x_1195; 
lean_dec(x_2);
x_1195 = !lean_is_exclusive(x_1190);
if (x_1195 == 0)
{
return x_1190;
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
x_1196 = lean_ctor_get(x_1190, 0);
x_1197 = lean_ctor_get(x_1190, 1);
lean_inc(x_1197);
lean_inc(x_1196);
lean_dec(x_1190);
x_1198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1198, 0, x_1196);
lean_ctor_set(x_1198, 1, x_1197);
return x_1198;
}
}
}
else
{
uint8_t x_1199; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_1199 = !lean_is_exclusive(x_1188);
if (x_1199 == 0)
{
return x_1188;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1200 = lean_ctor_get(x_1188, 0);
x_1201 = lean_ctor_get(x_1188, 1);
lean_inc(x_1201);
lean_inc(x_1200);
lean_dec(x_1188);
x_1202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1202, 0, x_1200);
lean_ctor_set(x_1202, 1, x_1201);
return x_1202;
}
}
}
}
}
}
}
else
{
uint8_t x_1298; 
lean_free_object(x_1);
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_1298 = !lean_is_exclusive(x_1149);
if (x_1298 == 0)
{
return x_1149;
}
else
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1299 = lean_ctor_get(x_1149, 0);
x_1300 = lean_ctor_get(x_1149, 1);
lean_inc(x_1300);
lean_inc(x_1299);
lean_dec(x_1149);
x_1301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1301, 0, x_1299);
lean_ctor_set(x_1301, 1, x_1300);
return x_1301;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1149) == 0)
{
lean_object* x_1302; lean_object* x_1303; 
x_1302 = lean_ctor_get(x_1149, 1);
lean_inc(x_1302);
lean_dec(x_1149);
if (x_1148 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1358; 
x_1358 = l_Lean_Expr_getOptParamDefault_x3f(x_96);
if (lean_obj_tag(x_1358) == 0)
{
lean_object* x_1359; 
x_1359 = l_Lean_Expr_getAutoParamTactic_x3f(x_96);
if (lean_obj_tag(x_1359) == 0)
{
lean_object* x_1360; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_1360 = lean_box(0);
x_1303 = x_1360;
goto block_1357;
}
else
{
lean_object* x_1361; 
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1361 = lean_ctor_get(x_1359, 0);
lean_inc(x_1361);
lean_dec(x_1359);
if (lean_obj_tag(x_1361) == 4)
{
lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
x_1362 = lean_ctor_get(x_1361, 0);
lean_inc(x_1362);
lean_dec(x_1361);
x_1363 = l_Lean_Elab_Term_getEnv___rarg(x_1302);
x_1364 = lean_ctor_get(x_1363, 0);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1363, 1);
lean_inc(x_1365);
lean_dec(x_1363);
x_1366 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1364, x_1362);
if (lean_obj_tag(x_1366) == 0)
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_1367 = lean_ctor_get(x_1366, 0);
lean_inc(x_1367);
lean_dec(x_1366);
x_1368 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1368, 0, x_1367);
x_1369 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1369, 0, x_1368);
x_1370 = l_Lean_Elab_Term_throwError___rarg(x_1369, x_4, x_1365);
return x_1370;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; 
x_1371 = lean_ctor_get(x_1366, 0);
lean_inc(x_1371);
lean_dec(x_1366);
x_1372 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1365);
x_1373 = lean_ctor_get(x_1372, 1);
lean_inc(x_1373);
lean_dec(x_1372);
x_1374 = l_Lean_Elab_Term_getMainModule___rarg(x_1373);
x_1375 = lean_ctor_get(x_1374, 1);
lean_inc(x_1375);
lean_dec(x_1374);
x_1376 = l_Lean_Syntax_getArgs(x_1371);
lean_dec(x_1371);
x_1377 = l_Array_empty___closed__1;
x_1378 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1376, x_1376, x_99, x_1377);
lean_dec(x_1376);
x_1379 = l_Lean_nullKind___closed__2;
x_1380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1380, 0, x_1379);
lean_ctor_set(x_1380, 1, x_1378);
x_1381 = lean_array_push(x_1377, x_1380);
x_1382 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_1383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1383, 0, x_1382);
lean_ctor_set(x_1383, 1, x_1381);
x_1384 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1385 = lean_array_push(x_1384, x_1383);
x_1386 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1387 = lean_array_push(x_1385, x_1386);
x_1388 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1389, 0, x_1388);
lean_ctor_set(x_1389, 1, x_1387);
x_1390 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_1391 = l_Lean_Expr_getAppNumArgsAux___main(x_96, x_99);
x_1392 = lean_nat_sub(x_1391, x_99);
lean_dec(x_1391);
x_1393 = lean_unsigned_to_nat(1u);
x_1394 = lean_nat_sub(x_1392, x_1393);
lean_dec(x_1392);
x_1395 = l_Lean_Expr_getRevArg_x21___main(x_96, x_1394);
lean_dec(x_96);
if (lean_obj_tag(x_1390) == 0)
{
lean_object* x_1396; lean_object* x_1397; 
x_1396 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1396, 0, x_1389);
lean_inc(x_4);
lean_inc(x_2);
x_1397 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1396, x_1395, x_4, x_1375);
if (lean_obj_tag(x_1397) == 0)
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
x_1398 = lean_ctor_get(x_1397, 0);
lean_inc(x_1398);
x_1399 = lean_ctor_get(x_1397, 1);
lean_inc(x_1399);
lean_dec(x_1397);
lean_inc(x_1398);
x_1400 = l_Lean_mkApp(x_2, x_1398);
x_1401 = lean_expr_instantiate1(x_97, x_1398);
lean_dec(x_1398);
lean_dec(x_97);
x_1 = x_1146;
x_2 = x_1400;
x_3 = x_1401;
x_5 = x_1399;
goto _start;
}
else
{
lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_1403 = lean_ctor_get(x_1397, 0);
lean_inc(x_1403);
x_1404 = lean_ctor_get(x_1397, 1);
lean_inc(x_1404);
if (lean_is_exclusive(x_1397)) {
 lean_ctor_release(x_1397, 0);
 lean_ctor_release(x_1397, 1);
 x_1405 = x_1397;
} else {
 lean_dec_ref(x_1397);
 x_1405 = lean_box(0);
}
if (lean_is_scalar(x_1405)) {
 x_1406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1406 = x_1405;
}
lean_ctor_set(x_1406, 0, x_1403);
lean_ctor_set(x_1406, 1, x_1404);
return x_1406;
}
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; 
x_1407 = lean_ctor_get(x_1390, 0);
lean_inc(x_1407);
lean_dec(x_1390);
x_1408 = l_Lean_Syntax_replaceInfo___main(x_1407, x_1389);
x_1409 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1409, 0, x_1408);
lean_inc(x_4);
lean_inc(x_2);
x_1410 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1409, x_1395, x_4, x_1375);
if (lean_obj_tag(x_1410) == 0)
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1411 = lean_ctor_get(x_1410, 0);
lean_inc(x_1411);
x_1412 = lean_ctor_get(x_1410, 1);
lean_inc(x_1412);
lean_dec(x_1410);
lean_inc(x_1411);
x_1413 = l_Lean_mkApp(x_2, x_1411);
x_1414 = lean_expr_instantiate1(x_97, x_1411);
lean_dec(x_1411);
lean_dec(x_97);
x_1 = x_1146;
x_2 = x_1413;
x_3 = x_1414;
x_5 = x_1412;
goto _start;
}
else
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_2);
x_1416 = lean_ctor_get(x_1410, 0);
lean_inc(x_1416);
x_1417 = lean_ctor_get(x_1410, 1);
lean_inc(x_1417);
if (lean_is_exclusive(x_1410)) {
 lean_ctor_release(x_1410, 0);
 lean_ctor_release(x_1410, 1);
 x_1418 = x_1410;
} else {
 lean_dec_ref(x_1410);
 x_1418 = lean_box(0);
}
if (lean_is_scalar(x_1418)) {
 x_1419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1419 = x_1418;
}
lean_ctor_set(x_1419, 0, x_1416);
lean_ctor_set(x_1419, 1, x_1417);
return x_1419;
}
}
}
}
else
{
lean_object* x_1420; lean_object* x_1421; 
lean_dec(x_1361);
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
lean_dec(x_2);
x_1420 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1421 = l_Lean_Elab_Term_throwError___rarg(x_1420, x_4, x_1302);
return x_1421;
}
}
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1422 = lean_ctor_get(x_1358, 0);
lean_inc(x_1422);
lean_dec(x_1358);
lean_inc(x_1422);
x_1423 = l_Lean_mkApp(x_2, x_1422);
x_1424 = lean_expr_instantiate1(x_97, x_1422);
lean_dec(x_1422);
lean_dec(x_97);
x_1 = x_1146;
x_2 = x_1423;
x_3 = x_1424;
x_5 = x_1302;
goto _start;
}
}
else
{
lean_object* x_1426; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_6);
x_1426 = lean_box(0);
x_1303 = x_1426;
goto block_1357;
}
}
else
{
lean_object* x_1427; lean_object* x_1428; 
lean_dec(x_1146);
lean_dec(x_95);
lean_dec(x_3);
x_1427 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_1428 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1427, x_96, x_4, x_1302);
if (lean_obj_tag(x_1428) == 0)
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
x_1429 = lean_ctor_get(x_1428, 0);
lean_inc(x_1429);
x_1430 = lean_ctor_get(x_1428, 1);
lean_inc(x_1430);
lean_dec(x_1428);
x_1431 = lean_unsigned_to_nat(1u);
x_1432 = lean_nat_add(x_10, x_1431);
lean_dec(x_10);
x_1433 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1433, 0, x_6);
lean_ctor_set(x_1433, 1, x_7);
lean_ctor_set(x_1433, 2, x_8);
lean_ctor_set(x_1433, 3, x_1432);
lean_ctor_set(x_1433, 4, x_11);
lean_ctor_set(x_1433, 5, x_12);
lean_ctor_set(x_1433, 6, x_13);
lean_ctor_set_uint8(x_1433, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1433, sizeof(void*)*7 + 1, x_1145);
lean_inc(x_1429);
x_1434 = l_Lean_mkApp(x_2, x_1429);
x_1435 = lean_expr_instantiate1(x_97, x_1429);
lean_dec(x_1429);
lean_dec(x_97);
x_1 = x_1433;
x_2 = x_1434;
x_3 = x_1435;
x_5 = x_1430;
goto _start;
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
lean_dec(x_97);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1437 = lean_ctor_get(x_1428, 0);
lean_inc(x_1437);
x_1438 = lean_ctor_get(x_1428, 1);
lean_inc(x_1438);
if (lean_is_exclusive(x_1428)) {
 lean_ctor_release(x_1428, 0);
 lean_ctor_release(x_1428, 1);
 x_1439 = x_1428;
} else {
 lean_dec_ref(x_1428);
 x_1439 = lean_box(0);
}
if (lean_is_scalar(x_1439)) {
 x_1440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1440 = x_1439;
}
lean_ctor_set(x_1440, 0, x_1437);
lean_ctor_set(x_1440, 1, x_1438);
return x_1440;
}
}
block_1357:
{
uint8_t x_1304; 
lean_dec(x_1303);
x_1304 = l_Array_isEmpty___rarg(x_11);
if (x_1304 == 0)
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1305 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1305, 0, x_95);
x_1306 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1307 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1307, 0, x_1306);
lean_ctor_set(x_1307, 1, x_1305);
x_1308 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1309 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1309, 0, x_1307);
lean_ctor_set(x_1309, 1, x_1308);
x_1310 = x_11;
x_1311 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_99, x_1310);
x_1312 = x_1311;
x_1313 = l_Array_toList___rarg(x_1312);
lean_dec(x_1312);
x_1314 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1313);
x_1315 = l_Array_HasRepr___rarg___closed__1;
x_1316 = lean_string_append(x_1315, x_1314);
lean_dec(x_1314);
x_1317 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1317, 0, x_1316);
x_1318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1318, 0, x_1317);
x_1319 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1319, 0, x_1309);
lean_ctor_set(x_1319, 1, x_1318);
x_1320 = l_Lean_Elab_Term_throwError___rarg(x_1319, x_4, x_1302);
return x_1320;
}
else
{
lean_object* x_1321; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; uint8_t x_1353; 
lean_dec(x_95);
lean_dec(x_11);
x_1346 = l_Lean_Elab_Term_getOptions(x_4, x_1302);
x_1347 = lean_ctor_get(x_1346, 0);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1346, 1);
lean_inc(x_1348);
lean_dec(x_1346);
x_1349 = l_Lean_Elab_Term_getCurrRef(x_4, x_1348);
x_1350 = lean_ctor_get(x_1349, 0);
lean_inc(x_1350);
x_1351 = lean_ctor_get(x_1349, 1);
lean_inc(x_1351);
lean_dec(x_1349);
x_1352 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1353 = l_Lean_checkTraceOption(x_1347, x_1352);
lean_dec(x_1347);
if (x_1353 == 0)
{
lean_dec(x_1350);
x_1321 = x_1351;
goto block_1345;
}
else
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
lean_inc(x_2);
x_1354 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1354, 0, x_2);
lean_inc(x_4);
x_1355 = l_Lean_Elab_Term_logTrace(x_1352, x_1350, x_1354, x_4, x_1351);
lean_dec(x_1350);
x_1356 = lean_ctor_get(x_1355, 1);
lean_inc(x_1356);
lean_dec(x_1355);
x_1321 = x_1356;
goto block_1345;
}
block_1345:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1322; 
lean_dec(x_3);
x_1322 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_1321);
lean_dec(x_12);
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; 
x_1323 = lean_ctor_get(x_1322, 1);
lean_inc(x_1323);
if (lean_is_exclusive(x_1322)) {
 lean_ctor_release(x_1322, 0);
 lean_ctor_release(x_1322, 1);
 x_1324 = x_1322;
} else {
 lean_dec_ref(x_1322);
 x_1324 = lean_box(0);
}
if (lean_is_scalar(x_1324)) {
 x_1325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1325 = x_1324;
}
lean_ctor_set(x_1325, 0, x_2);
lean_ctor_set(x_1325, 1, x_1323);
return x_1325;
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
lean_dec(x_2);
x_1326 = lean_ctor_get(x_1322, 0);
lean_inc(x_1326);
x_1327 = lean_ctor_get(x_1322, 1);
lean_inc(x_1327);
if (lean_is_exclusive(x_1322)) {
 lean_ctor_release(x_1322, 0);
 lean_ctor_release(x_1322, 1);
 x_1328 = x_1322;
} else {
 lean_dec_ref(x_1322);
 x_1328 = lean_box(0);
}
if (lean_is_scalar(x_1328)) {
 x_1329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1329 = x_1328;
}
lean_ctor_set(x_1329, 0, x_1326);
lean_ctor_set(x_1329, 1, x_1327);
return x_1329;
}
}
else
{
lean_object* x_1330; lean_object* x_1331; 
x_1330 = lean_ctor_get(x_8, 0);
lean_inc(x_1330);
lean_dec(x_8);
lean_inc(x_4);
x_1331 = l_Lean_Elab_Term_isDefEq(x_1330, x_3, x_4, x_1321);
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1332; lean_object* x_1333; 
x_1332 = lean_ctor_get(x_1331, 1);
lean_inc(x_1332);
lean_dec(x_1331);
x_1333 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_99, x_4, x_1332);
lean_dec(x_12);
if (lean_obj_tag(x_1333) == 0)
{
lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
x_1334 = lean_ctor_get(x_1333, 1);
lean_inc(x_1334);
if (lean_is_exclusive(x_1333)) {
 lean_ctor_release(x_1333, 0);
 lean_ctor_release(x_1333, 1);
 x_1335 = x_1333;
} else {
 lean_dec_ref(x_1333);
 x_1335 = lean_box(0);
}
if (lean_is_scalar(x_1335)) {
 x_1336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1336 = x_1335;
}
lean_ctor_set(x_1336, 0, x_2);
lean_ctor_set(x_1336, 1, x_1334);
return x_1336;
}
else
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
lean_dec(x_2);
x_1337 = lean_ctor_get(x_1333, 0);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1333, 1);
lean_inc(x_1338);
if (lean_is_exclusive(x_1333)) {
 lean_ctor_release(x_1333, 0);
 lean_ctor_release(x_1333, 1);
 x_1339 = x_1333;
} else {
 lean_dec_ref(x_1333);
 x_1339 = lean_box(0);
}
if (lean_is_scalar(x_1339)) {
 x_1340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1340 = x_1339;
}
lean_ctor_set(x_1340, 0, x_1337);
lean_ctor_set(x_1340, 1, x_1338);
return x_1340;
}
}
else
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_1341 = lean_ctor_get(x_1331, 0);
lean_inc(x_1341);
x_1342 = lean_ctor_get(x_1331, 1);
lean_inc(x_1342);
if (lean_is_exclusive(x_1331)) {
 lean_ctor_release(x_1331, 0);
 lean_ctor_release(x_1331, 1);
 x_1343 = x_1331;
} else {
 lean_dec_ref(x_1331);
 x_1343 = lean_box(0);
}
if (lean_is_scalar(x_1343)) {
 x_1344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1344 = x_1343;
}
lean_ctor_set(x_1344, 0, x_1341);
lean_ctor_set(x_1344, 1, x_1342);
return x_1344;
}
}
}
}
}
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; 
lean_dec(x_1146);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
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
x_1441 = lean_ctor_get(x_1149, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1149, 1);
lean_inc(x_1442);
if (lean_is_exclusive(x_1149)) {
 lean_ctor_release(x_1149, 0);
 lean_ctor_release(x_1149, 1);
 x_1443 = x_1149;
} else {
 lean_dec_ref(x_1149);
 x_1443 = lean_box(0);
}
if (lean_is_scalar(x_1443)) {
 x_1444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1444 = x_1443;
}
lean_ctor_set(x_1444, 0, x_1441);
lean_ctor_set(x_1444, 1, x_1442);
return x_1444;
}
}
}
}
}
else
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
lean_dec(x_95);
lean_dec(x_3);
x_1445 = lean_ctor_get(x_100, 0);
lean_inc(x_1445);
lean_dec(x_100);
x_1446 = l_Lean_Elab_Term_NamedArg_inhabited;
x_1447 = lean_array_get(x_1446, x_11, x_1445);
x_1448 = l_Array_eraseIdx___rarg(x_11, x_1445);
lean_dec(x_1445);
x_1449 = lean_ctor_get(x_1447, 1);
lean_inc(x_1449);
lean_dec(x_1447);
lean_inc(x_4);
lean_inc(x_2);
x_1450 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1449, x_96, x_4, x_19);
if (lean_obj_tag(x_1450) == 0)
{
lean_object* x_1451; lean_object* x_1452; uint8_t x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
x_1451 = lean_ctor_get(x_1450, 0);
lean_inc(x_1451);
x_1452 = lean_ctor_get(x_1450, 1);
lean_inc(x_1452);
lean_dec(x_1450);
x_1453 = 1;
x_1454 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1454, 0, x_6);
lean_ctor_set(x_1454, 1, x_7);
lean_ctor_set(x_1454, 2, x_8);
lean_ctor_set(x_1454, 3, x_10);
lean_ctor_set(x_1454, 4, x_1448);
lean_ctor_set(x_1454, 5, x_12);
lean_ctor_set(x_1454, 6, x_13);
lean_ctor_set_uint8(x_1454, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1454, sizeof(void*)*7 + 1, x_1453);
lean_inc(x_1451);
x_1455 = l_Lean_mkApp(x_2, x_1451);
x_1456 = lean_expr_instantiate1(x_97, x_1451);
lean_dec(x_1451);
lean_dec(x_97);
lean_inc(x_4);
x_1457 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_18, x_4, x_1452);
if (lean_obj_tag(x_1457) == 0)
{
lean_object* x_1458; 
x_1458 = lean_ctor_get(x_1457, 1);
lean_inc(x_1458);
lean_dec(x_1457);
x_1 = x_1454;
x_2 = x_1455;
x_3 = x_1456;
x_5 = x_1458;
goto _start;
}
else
{
uint8_t x_1460; 
lean_dec(x_1456);
lean_dec(x_1455);
lean_dec(x_1454);
lean_dec(x_4);
x_1460 = !lean_is_exclusive(x_1457);
if (x_1460 == 0)
{
return x_1457;
}
else
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
x_1461 = lean_ctor_get(x_1457, 0);
x_1462 = lean_ctor_get(x_1457, 1);
lean_inc(x_1462);
lean_inc(x_1461);
lean_dec(x_1457);
x_1463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1463, 0, x_1461);
lean_ctor_set(x_1463, 1, x_1462);
return x_1463;
}
}
}
else
{
uint8_t x_1464; 
lean_dec(x_1448);
lean_dec(x_97);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_1464 = !lean_is_exclusive(x_1450);
if (x_1464 == 0)
{
return x_1450;
}
else
{
lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; 
x_1465 = lean_ctor_get(x_1450, 0);
x_1466 = lean_ctor_get(x_1450, 1);
lean_inc(x_1466);
lean_inc(x_1465);
lean_dec(x_1450);
x_1467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1467, 0, x_1465);
lean_ctor_set(x_1467, 1, x_1466);
return x_1467;
}
}
}
}
else
{
lean_object* x_1468; 
lean_dec(x_13);
lean_dec(x_6);
x_1468 = lean_box(0);
x_20 = x_1468;
goto block_94;
}
block_94:
{
uint8_t x_21; 
lean_dec(x_20);
x_21 = l_Array_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_inc(x_4);
x_22 = l___private_Lean_Elab_App_4__tryCoeFun(x_18, x_2, x_4, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_4);
lean_inc(x_23);
x_25 = l_Lean_Elab_Term_inferType(x_23, x_4, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_2 = x_23;
x_3 = x_26;
x_5 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_array_get_size(x_7);
lean_dec(x_7);
x_38 = lean_nat_dec_eq(x_10, x_37);
lean_dec(x_37);
lean_dec(x_10);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_inc(x_4);
x_39 = l___private_Lean_Elab_App_4__tryCoeFun(x_18, x_2, x_4, x_19);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_4);
lean_inc(x_40);
x_42 = l_Lean_Elab_Term_inferType(x_40, x_4, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_2 = x_40;
x_3 = x_43;
x_5 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_4);
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
lean_dec(x_4);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_18);
lean_dec(x_1);
x_83 = l_Lean_Elab_Term_getOptions(x_4, x_19);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Elab_Term_getCurrRef(x_4, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_90 = l_Lean_checkTraceOption(x_84, x_89);
lean_dec(x_84);
if (x_90 == 0)
{
lean_dec(x_87);
x_54 = x_88;
goto block_82;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_inc(x_2);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_2);
lean_inc(x_4);
x_92 = l_Lean_Elab_Term_logTrace(x_89, x_87, x_91, x_4, x_88);
lean_dec(x_87);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_54 = x_93;
goto block_82;
}
block_82:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_55, x_4, x_54);
lean_dec(x_12);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_2);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_8, 0);
lean_inc(x_65);
lean_dec(x_8);
lean_inc(x_4);
x_66 = l_Lean_Elab_Term_isDefEq(x_65, x_3, x_4, x_54);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_68, x_4, x_67);
lean_dec(x_12);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
lean_ctor_set(x_69, 0, x_2);
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_69);
if (x_74 == 0)
{
return x_69;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_69, 0);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
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
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_66);
if (x_78 == 0)
{
return x_66;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_66, 0);
x_80 = lean_ctor_get(x_66, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_66);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
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
uint8_t x_1469; 
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
x_1469 = !lean_is_exclusive(x_17);
if (x_1469 == 0)
{
return x_17;
}
else
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; 
x_1470 = lean_ctor_get(x_17, 0);
x_1471 = lean_ctor_get(x_17, 1);
lean_inc(x_1471);
lean_inc(x_1470);
lean_dec(x_17);
x_1472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1472, 0, x_1470);
lean_ctor_set(x_1472, 1, x_1471);
return x_1472;
}
}
}
else
{
uint8_t x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; uint8_t x_1484; uint8_t x_1485; uint8_t x_1486; lean_object* x_1487; lean_object* x_1488; 
x_1473 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_1474 = lean_ctor_get(x_4, 0);
x_1475 = lean_ctor_get(x_4, 1);
x_1476 = lean_ctor_get(x_4, 2);
x_1477 = lean_ctor_get(x_4, 3);
x_1478 = lean_ctor_get(x_4, 4);
x_1479 = lean_ctor_get(x_4, 5);
x_1480 = lean_ctor_get(x_4, 6);
x_1481 = lean_ctor_get(x_4, 7);
x_1482 = lean_ctor_get(x_4, 8);
x_1483 = lean_ctor_get(x_4, 9);
x_1484 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
x_1485 = lean_ctor_get_uint8(x_4, sizeof(void*)*11 + 1);
x_1486 = lean_ctor_get_uint8(x_4, sizeof(void*)*11 + 2);
lean_inc(x_1483);
lean_inc(x_1482);
lean_inc(x_1481);
lean_inc(x_1480);
lean_inc(x_1479);
lean_inc(x_1478);
lean_inc(x_1477);
lean_inc(x_1476);
lean_inc(x_1475);
lean_inc(x_1474);
lean_dec(x_4);
lean_inc(x_6);
x_1487 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_1487, 0, x_1474);
lean_ctor_set(x_1487, 1, x_1475);
lean_ctor_set(x_1487, 2, x_1476);
lean_ctor_set(x_1487, 3, x_1477);
lean_ctor_set(x_1487, 4, x_1478);
lean_ctor_set(x_1487, 5, x_1479);
lean_ctor_set(x_1487, 6, x_1480);
lean_ctor_set(x_1487, 7, x_1481);
lean_ctor_set(x_1487, 8, x_1482);
lean_ctor_set(x_1487, 9, x_1483);
lean_ctor_set(x_1487, 10, x_6);
lean_ctor_set_uint8(x_1487, sizeof(void*)*11, x_1484);
lean_ctor_set_uint8(x_1487, sizeof(void*)*11 + 1, x_1485);
lean_ctor_set_uint8(x_1487, sizeof(void*)*11 + 2, x_1486);
lean_inc(x_1487);
lean_inc(x_3);
x_1488 = l_Lean_Elab_Term_whnfForall(x_3, x_1487, x_5);
if (lean_obj_tag(x_1488) == 0)
{
lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1489 = lean_ctor_get(x_1488, 0);
lean_inc(x_1489);
x_1490 = lean_ctor_get(x_1488, 1);
lean_inc(x_1490);
lean_dec(x_1488);
if (lean_obj_tag(x_1489) == 7)
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; uint64_t x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1564 = lean_ctor_get(x_1489, 0);
lean_inc(x_1564);
x_1565 = lean_ctor_get(x_1489, 1);
lean_inc(x_1565);
x_1566 = lean_ctor_get(x_1489, 2);
lean_inc(x_1566);
x_1567 = lean_ctor_get_uint64(x_1489, sizeof(void*)*3);
x_1568 = lean_unsigned_to_nat(0u);
x_1569 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_1564, x_11, x_1568);
if (lean_obj_tag(x_1569) == 0)
{
uint8_t x_1570; 
x_1570 = (uint8_t)((x_1567 << 24) >> 61);
switch (x_1570) {
case 0:
{
uint8_t x_1571; lean_object* x_1572; lean_object* x_1573; uint8_t x_1574; lean_object* x_1575; lean_object* x_1576; 
x_1571 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1572 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1572, 0, x_6);
lean_ctor_set(x_1572, 1, x_7);
lean_ctor_set(x_1572, 2, x_8);
lean_ctor_set(x_1572, 3, x_10);
lean_ctor_set(x_1572, 4, x_11);
lean_ctor_set(x_1572, 5, x_12);
lean_ctor_set(x_1572, 6, x_13);
lean_ctor_set_uint8(x_1572, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1572, sizeof(void*)*7 + 1, x_1571);
x_1573 = lean_array_get_size(x_7);
x_1574 = lean_nat_dec_lt(x_10, x_1573);
lean_dec(x_1573);
lean_inc(x_1487);
lean_inc(x_1);
x_1575 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1489, x_1487, x_1490);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1576 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1576 = lean_box(0);
}
if (lean_obj_tag(x_1575) == 0)
{
lean_object* x_1577; lean_object* x_1578; 
x_1577 = lean_ctor_get(x_1575, 1);
lean_inc(x_1577);
lean_dec(x_1575);
if (x_1574 == 0)
{
lean_dec(x_1576);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1633; 
x_1633 = l_Lean_Expr_getOptParamDefault_x3f(x_1565);
if (lean_obj_tag(x_1633) == 0)
{
lean_object* x_1634; 
x_1634 = l_Lean_Expr_getAutoParamTactic_x3f(x_1565);
if (lean_obj_tag(x_1634) == 0)
{
lean_object* x_1635; 
lean_dec(x_1572);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
x_1635 = lean_box(0);
x_1578 = x_1635;
goto block_1632;
}
else
{
lean_object* x_1636; 
lean_dec(x_1564);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1636 = lean_ctor_get(x_1634, 0);
lean_inc(x_1636);
lean_dec(x_1634);
if (lean_obj_tag(x_1636) == 4)
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; 
x_1637 = lean_ctor_get(x_1636, 0);
lean_inc(x_1637);
lean_dec(x_1636);
x_1638 = l_Lean_Elab_Term_getEnv___rarg(x_1577);
x_1639 = lean_ctor_get(x_1638, 0);
lean_inc(x_1639);
x_1640 = lean_ctor_get(x_1638, 1);
lean_inc(x_1640);
lean_dec(x_1638);
x_1641 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1639, x_1637);
if (lean_obj_tag(x_1641) == 0)
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; 
lean_dec(x_1572);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
lean_dec(x_2);
x_1642 = lean_ctor_get(x_1641, 0);
lean_inc(x_1642);
lean_dec(x_1641);
x_1643 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1643, 0, x_1642);
x_1644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1644, 0, x_1643);
x_1645 = l_Lean_Elab_Term_throwError___rarg(x_1644, x_1487, x_1640);
return x_1645;
}
else
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; 
x_1646 = lean_ctor_get(x_1641, 0);
lean_inc(x_1646);
lean_dec(x_1641);
x_1647 = l_Lean_Elab_Term_getCurrMacroScope(x_1487, x_1640);
x_1648 = lean_ctor_get(x_1647, 1);
lean_inc(x_1648);
lean_dec(x_1647);
x_1649 = l_Lean_Elab_Term_getMainModule___rarg(x_1648);
x_1650 = lean_ctor_get(x_1649, 1);
lean_inc(x_1650);
lean_dec(x_1649);
x_1651 = l_Lean_Syntax_getArgs(x_1646);
lean_dec(x_1646);
x_1652 = l_Array_empty___closed__1;
x_1653 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1651, x_1651, x_1568, x_1652);
lean_dec(x_1651);
x_1654 = l_Lean_nullKind___closed__2;
x_1655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1655, 0, x_1654);
lean_ctor_set(x_1655, 1, x_1653);
x_1656 = lean_array_push(x_1652, x_1655);
x_1657 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_1658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1658, 0, x_1657);
lean_ctor_set(x_1658, 1, x_1656);
x_1659 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1660 = lean_array_push(x_1659, x_1658);
x_1661 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1662 = lean_array_push(x_1660, x_1661);
x_1663 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1664, 0, x_1663);
lean_ctor_set(x_1664, 1, x_1662);
x_1665 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_1666 = l_Lean_Expr_getAppNumArgsAux___main(x_1565, x_1568);
x_1667 = lean_nat_sub(x_1666, x_1568);
lean_dec(x_1666);
x_1668 = lean_unsigned_to_nat(1u);
x_1669 = lean_nat_sub(x_1667, x_1668);
lean_dec(x_1667);
x_1670 = l_Lean_Expr_getRevArg_x21___main(x_1565, x_1669);
lean_dec(x_1565);
if (lean_obj_tag(x_1665) == 0)
{
lean_object* x_1671; lean_object* x_1672; 
x_1671 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1671, 0, x_1664);
lean_inc(x_1487);
lean_inc(x_2);
x_1672 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1671, x_1670, x_1487, x_1650);
if (lean_obj_tag(x_1672) == 0)
{
lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; 
x_1673 = lean_ctor_get(x_1672, 0);
lean_inc(x_1673);
x_1674 = lean_ctor_get(x_1672, 1);
lean_inc(x_1674);
lean_dec(x_1672);
lean_inc(x_1673);
x_1675 = l_Lean_mkApp(x_2, x_1673);
x_1676 = lean_expr_instantiate1(x_1566, x_1673);
lean_dec(x_1673);
lean_dec(x_1566);
x_1 = x_1572;
x_2 = x_1675;
x_3 = x_1676;
x_4 = x_1487;
x_5 = x_1674;
goto _start;
}
else
{
lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; 
lean_dec(x_1572);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_2);
x_1678 = lean_ctor_get(x_1672, 0);
lean_inc(x_1678);
x_1679 = lean_ctor_get(x_1672, 1);
lean_inc(x_1679);
if (lean_is_exclusive(x_1672)) {
 lean_ctor_release(x_1672, 0);
 lean_ctor_release(x_1672, 1);
 x_1680 = x_1672;
} else {
 lean_dec_ref(x_1672);
 x_1680 = lean_box(0);
}
if (lean_is_scalar(x_1680)) {
 x_1681 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1681 = x_1680;
}
lean_ctor_set(x_1681, 0, x_1678);
lean_ctor_set(x_1681, 1, x_1679);
return x_1681;
}
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
x_1682 = lean_ctor_get(x_1665, 0);
lean_inc(x_1682);
lean_dec(x_1665);
x_1683 = l_Lean_Syntax_replaceInfo___main(x_1682, x_1664);
x_1684 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1684, 0, x_1683);
lean_inc(x_1487);
lean_inc(x_2);
x_1685 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1684, x_1670, x_1487, x_1650);
if (lean_obj_tag(x_1685) == 0)
{
lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
x_1686 = lean_ctor_get(x_1685, 0);
lean_inc(x_1686);
x_1687 = lean_ctor_get(x_1685, 1);
lean_inc(x_1687);
lean_dec(x_1685);
lean_inc(x_1686);
x_1688 = l_Lean_mkApp(x_2, x_1686);
x_1689 = lean_expr_instantiate1(x_1566, x_1686);
lean_dec(x_1686);
lean_dec(x_1566);
x_1 = x_1572;
x_2 = x_1688;
x_3 = x_1689;
x_4 = x_1487;
x_5 = x_1687;
goto _start;
}
else
{
lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; 
lean_dec(x_1572);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_2);
x_1691 = lean_ctor_get(x_1685, 0);
lean_inc(x_1691);
x_1692 = lean_ctor_get(x_1685, 1);
lean_inc(x_1692);
if (lean_is_exclusive(x_1685)) {
 lean_ctor_release(x_1685, 0);
 lean_ctor_release(x_1685, 1);
 x_1693 = x_1685;
} else {
 lean_dec_ref(x_1685);
 x_1693 = lean_box(0);
}
if (lean_is_scalar(x_1693)) {
 x_1694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1694 = x_1693;
}
lean_ctor_set(x_1694, 0, x_1691);
lean_ctor_set(x_1694, 1, x_1692);
return x_1694;
}
}
}
}
else
{
lean_object* x_1695; lean_object* x_1696; 
lean_dec(x_1636);
lean_dec(x_1572);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
lean_dec(x_2);
x_1695 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1696 = l_Lean_Elab_Term_throwError___rarg(x_1695, x_1487, x_1577);
return x_1696;
}
}
}
else
{
lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; 
lean_dec(x_1565);
lean_dec(x_1564);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1697 = lean_ctor_get(x_1633, 0);
lean_inc(x_1697);
lean_dec(x_1633);
lean_inc(x_1697);
x_1698 = l_Lean_mkApp(x_2, x_1697);
x_1699 = lean_expr_instantiate1(x_1566, x_1697);
lean_dec(x_1697);
lean_dec(x_1566);
x_1 = x_1572;
x_2 = x_1698;
x_3 = x_1699;
x_4 = x_1487;
x_5 = x_1577;
goto _start;
}
}
else
{
lean_object* x_1701; 
lean_dec(x_1572);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
x_1701 = lean_box(0);
x_1578 = x_1701;
goto block_1632;
}
}
else
{
lean_object* x_1702; lean_object* x_1703; 
lean_dec(x_1572);
lean_dec(x_1564);
lean_dec(x_3);
x_1702 = lean_array_fget(x_7, x_10);
lean_inc(x_1487);
lean_inc(x_2);
x_1703 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1702, x_1565, x_1487, x_1577);
if (lean_obj_tag(x_1703) == 0)
{
lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; 
x_1704 = lean_ctor_get(x_1703, 0);
lean_inc(x_1704);
x_1705 = lean_ctor_get(x_1703, 1);
lean_inc(x_1705);
lean_dec(x_1703);
x_1706 = lean_unsigned_to_nat(1u);
x_1707 = lean_nat_add(x_10, x_1706);
lean_dec(x_10);
if (lean_is_scalar(x_1576)) {
 x_1708 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1708 = x_1576;
}
lean_ctor_set(x_1708, 0, x_6);
lean_ctor_set(x_1708, 1, x_7);
lean_ctor_set(x_1708, 2, x_8);
lean_ctor_set(x_1708, 3, x_1707);
lean_ctor_set(x_1708, 4, x_11);
lean_ctor_set(x_1708, 5, x_12);
lean_ctor_set(x_1708, 6, x_13);
lean_ctor_set_uint8(x_1708, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1708, sizeof(void*)*7 + 1, x_1571);
lean_inc(x_1704);
x_1709 = l_Lean_mkApp(x_2, x_1704);
x_1710 = lean_expr_instantiate1(x_1566, x_1704);
lean_dec(x_1704);
lean_dec(x_1566);
x_1 = x_1708;
x_2 = x_1709;
x_3 = x_1710;
x_4 = x_1487;
x_5 = x_1705;
goto _start;
}
else
{
lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; 
lean_dec(x_1576);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1712 = lean_ctor_get(x_1703, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1703, 1);
lean_inc(x_1713);
if (lean_is_exclusive(x_1703)) {
 lean_ctor_release(x_1703, 0);
 lean_ctor_release(x_1703, 1);
 x_1714 = x_1703;
} else {
 lean_dec_ref(x_1703);
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
block_1632:
{
uint8_t x_1579; 
lean_dec(x_1578);
x_1579 = l_Array_isEmpty___rarg(x_11);
if (x_1579 == 0)
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1580 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1580, 0, x_1564);
x_1581 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1582 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1582, 0, x_1581);
lean_ctor_set(x_1582, 1, x_1580);
x_1583 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1584 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1584, 0, x_1582);
lean_ctor_set(x_1584, 1, x_1583);
x_1585 = x_11;
x_1586 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1568, x_1585);
x_1587 = x_1586;
x_1588 = l_Array_toList___rarg(x_1587);
lean_dec(x_1587);
x_1589 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1588);
x_1590 = l_Array_HasRepr___rarg___closed__1;
x_1591 = lean_string_append(x_1590, x_1589);
lean_dec(x_1589);
x_1592 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1592, 0, x_1591);
x_1593 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1593, 0, x_1592);
x_1594 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1594, 0, x_1584);
lean_ctor_set(x_1594, 1, x_1593);
x_1595 = l_Lean_Elab_Term_throwError___rarg(x_1594, x_1487, x_1577);
return x_1595;
}
else
{
lean_object* x_1596; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; uint8_t x_1628; 
lean_dec(x_1564);
lean_dec(x_11);
x_1621 = l_Lean_Elab_Term_getOptions(x_1487, x_1577);
x_1622 = lean_ctor_get(x_1621, 0);
lean_inc(x_1622);
x_1623 = lean_ctor_get(x_1621, 1);
lean_inc(x_1623);
lean_dec(x_1621);
x_1624 = l_Lean_Elab_Term_getCurrRef(x_1487, x_1623);
x_1625 = lean_ctor_get(x_1624, 0);
lean_inc(x_1625);
x_1626 = lean_ctor_get(x_1624, 1);
lean_inc(x_1626);
lean_dec(x_1624);
x_1627 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1628 = l_Lean_checkTraceOption(x_1622, x_1627);
lean_dec(x_1622);
if (x_1628 == 0)
{
lean_dec(x_1625);
x_1596 = x_1626;
goto block_1620;
}
else
{
lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; 
lean_inc(x_2);
x_1629 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1629, 0, x_2);
lean_inc(x_1487);
x_1630 = l_Lean_Elab_Term_logTrace(x_1627, x_1625, x_1629, x_1487, x_1626);
lean_dec(x_1625);
x_1631 = lean_ctor_get(x_1630, 1);
lean_inc(x_1631);
lean_dec(x_1630);
x_1596 = x_1631;
goto block_1620;
}
block_1620:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1597; 
lean_dec(x_3);
x_1597 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_1596);
lean_dec(x_12);
if (lean_obj_tag(x_1597) == 0)
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; 
x_1598 = lean_ctor_get(x_1597, 1);
lean_inc(x_1598);
if (lean_is_exclusive(x_1597)) {
 lean_ctor_release(x_1597, 0);
 lean_ctor_release(x_1597, 1);
 x_1599 = x_1597;
} else {
 lean_dec_ref(x_1597);
 x_1599 = lean_box(0);
}
if (lean_is_scalar(x_1599)) {
 x_1600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1600 = x_1599;
}
lean_ctor_set(x_1600, 0, x_2);
lean_ctor_set(x_1600, 1, x_1598);
return x_1600;
}
else
{
lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; 
lean_dec(x_2);
x_1601 = lean_ctor_get(x_1597, 0);
lean_inc(x_1601);
x_1602 = lean_ctor_get(x_1597, 1);
lean_inc(x_1602);
if (lean_is_exclusive(x_1597)) {
 lean_ctor_release(x_1597, 0);
 lean_ctor_release(x_1597, 1);
 x_1603 = x_1597;
} else {
 lean_dec_ref(x_1597);
 x_1603 = lean_box(0);
}
if (lean_is_scalar(x_1603)) {
 x_1604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1604 = x_1603;
}
lean_ctor_set(x_1604, 0, x_1601);
lean_ctor_set(x_1604, 1, x_1602);
return x_1604;
}
}
else
{
lean_object* x_1605; lean_object* x_1606; 
x_1605 = lean_ctor_get(x_8, 0);
lean_inc(x_1605);
lean_dec(x_8);
lean_inc(x_1487);
x_1606 = l_Lean_Elab_Term_isDefEq(x_1605, x_3, x_1487, x_1596);
if (lean_obj_tag(x_1606) == 0)
{
lean_object* x_1607; lean_object* x_1608; 
x_1607 = lean_ctor_get(x_1606, 1);
lean_inc(x_1607);
lean_dec(x_1606);
x_1608 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_1607);
lean_dec(x_12);
if (lean_obj_tag(x_1608) == 0)
{
lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; 
x_1609 = lean_ctor_get(x_1608, 1);
lean_inc(x_1609);
if (lean_is_exclusive(x_1608)) {
 lean_ctor_release(x_1608, 0);
 lean_ctor_release(x_1608, 1);
 x_1610 = x_1608;
} else {
 lean_dec_ref(x_1608);
 x_1610 = lean_box(0);
}
if (lean_is_scalar(x_1610)) {
 x_1611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1611 = x_1610;
}
lean_ctor_set(x_1611, 0, x_2);
lean_ctor_set(x_1611, 1, x_1609);
return x_1611;
}
else
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; 
lean_dec(x_2);
x_1612 = lean_ctor_get(x_1608, 0);
lean_inc(x_1612);
x_1613 = lean_ctor_get(x_1608, 1);
lean_inc(x_1613);
if (lean_is_exclusive(x_1608)) {
 lean_ctor_release(x_1608, 0);
 lean_ctor_release(x_1608, 1);
 x_1614 = x_1608;
} else {
 lean_dec_ref(x_1608);
 x_1614 = lean_box(0);
}
if (lean_is_scalar(x_1614)) {
 x_1615 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1615 = x_1614;
}
lean_ctor_set(x_1615, 0, x_1612);
lean_ctor_set(x_1615, 1, x_1613);
return x_1615;
}
}
else
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; 
lean_dec(x_1487);
lean_dec(x_12);
lean_dec(x_2);
x_1616 = lean_ctor_get(x_1606, 0);
lean_inc(x_1616);
x_1617 = lean_ctor_get(x_1606, 1);
lean_inc(x_1617);
if (lean_is_exclusive(x_1606)) {
 lean_ctor_release(x_1606, 0);
 lean_ctor_release(x_1606, 1);
 x_1618 = x_1606;
} else {
 lean_dec_ref(x_1606);
 x_1618 = lean_box(0);
}
if (lean_is_scalar(x_1618)) {
 x_1619 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1619 = x_1618;
}
lean_ctor_set(x_1619, 0, x_1616);
lean_ctor_set(x_1619, 1, x_1617);
return x_1619;
}
}
}
}
}
}
else
{
lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; 
lean_dec(x_1576);
lean_dec(x_1572);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_1564);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_1716 = lean_ctor_get(x_1575, 0);
lean_inc(x_1716);
x_1717 = lean_ctor_get(x_1575, 1);
lean_inc(x_1717);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 x_1718 = x_1575;
} else {
 lean_dec_ref(x_1575);
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
case 1:
{
if (x_9 == 0)
{
lean_object* x_1720; lean_object* x_1721; uint8_t x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; 
lean_dec(x_1564);
lean_dec(x_1489);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1720 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1720 = lean_box(0);
}
x_1721 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1721, 0, x_1565);
x_1722 = 0;
x_1723 = lean_box(0);
lean_inc(x_1487);
x_1724 = l_Lean_Elab_Term_mkFreshExprMVar(x_1721, x_1722, x_1723, x_1487, x_1490);
x_1725 = lean_ctor_get(x_1724, 0);
lean_inc(x_1725);
x_1726 = lean_ctor_get(x_1724, 1);
lean_inc(x_1726);
lean_dec(x_1724);
lean_inc(x_1487);
lean_inc(x_1725);
x_1727 = l_Lean_Elab_Term_isTypeFormer(x_1725, x_1487, x_1726);
if (lean_obj_tag(x_1727) == 0)
{
lean_object* x_1728; uint8_t x_1729; 
x_1728 = lean_ctor_get(x_1727, 0);
lean_inc(x_1728);
x_1729 = lean_unbox(x_1728);
lean_dec(x_1728);
if (x_1729 == 0)
{
lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; 
x_1730 = lean_ctor_get(x_1727, 1);
lean_inc(x_1730);
lean_dec(x_1727);
if (lean_is_scalar(x_1720)) {
 x_1731 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1731 = x_1720;
}
lean_ctor_set(x_1731, 0, x_6);
lean_ctor_set(x_1731, 1, x_7);
lean_ctor_set(x_1731, 2, x_8);
lean_ctor_set(x_1731, 3, x_10);
lean_ctor_set(x_1731, 4, x_11);
lean_ctor_set(x_1731, 5, x_12);
lean_ctor_set(x_1731, 6, x_13);
lean_ctor_set_uint8(x_1731, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1731, sizeof(void*)*7 + 1, x_1473);
lean_inc(x_1725);
x_1732 = l_Lean_mkApp(x_2, x_1725);
x_1733 = lean_expr_instantiate1(x_1566, x_1725);
lean_dec(x_1725);
lean_dec(x_1566);
x_1 = x_1731;
x_2 = x_1732;
x_3 = x_1733;
x_4 = x_1487;
x_5 = x_1730;
goto _start;
}
else
{
lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; 
x_1735 = lean_ctor_get(x_1727, 1);
lean_inc(x_1735);
lean_dec(x_1727);
x_1736 = l_Lean_Expr_mvarId_x21(x_1725);
x_1737 = lean_array_push(x_13, x_1736);
if (lean_is_scalar(x_1720)) {
 x_1738 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1738 = x_1720;
}
lean_ctor_set(x_1738, 0, x_6);
lean_ctor_set(x_1738, 1, x_7);
lean_ctor_set(x_1738, 2, x_8);
lean_ctor_set(x_1738, 3, x_10);
lean_ctor_set(x_1738, 4, x_11);
lean_ctor_set(x_1738, 5, x_12);
lean_ctor_set(x_1738, 6, x_1737);
lean_ctor_set_uint8(x_1738, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1738, sizeof(void*)*7 + 1, x_1473);
lean_inc(x_1725);
x_1739 = l_Lean_mkApp(x_2, x_1725);
x_1740 = lean_expr_instantiate1(x_1566, x_1725);
lean_dec(x_1725);
lean_dec(x_1566);
x_1 = x_1738;
x_2 = x_1739;
x_3 = x_1740;
x_4 = x_1487;
x_5 = x_1735;
goto _start;
}
}
else
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; 
lean_dec(x_1725);
lean_dec(x_1720);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1742 = lean_ctor_get(x_1727, 0);
lean_inc(x_1742);
x_1743 = lean_ctor_get(x_1727, 1);
lean_inc(x_1743);
if (lean_is_exclusive(x_1727)) {
 lean_ctor_release(x_1727, 0);
 lean_ctor_release(x_1727, 1);
 x_1744 = x_1727;
} else {
 lean_dec_ref(x_1727);
 x_1744 = lean_box(0);
}
if (lean_is_scalar(x_1744)) {
 x_1745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1745 = x_1744;
}
lean_ctor_set(x_1745, 0, x_1742);
lean_ctor_set(x_1745, 1, x_1743);
return x_1745;
}
}
else
{
lean_object* x_1746; uint8_t x_1747; lean_object* x_1748; lean_object* x_1749; 
x_1746 = lean_array_get_size(x_7);
x_1747 = lean_nat_dec_lt(x_10, x_1746);
lean_dec(x_1746);
lean_inc(x_1487);
lean_inc(x_1);
x_1748 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1489, x_1487, x_1490);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1749 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1749 = lean_box(0);
}
if (lean_obj_tag(x_1748) == 0)
{
if (x_1747 == 0)
{
lean_object* x_1750; uint8_t x_1751; 
lean_dec(x_1749);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_1750 = lean_ctor_get(x_1748, 1);
lean_inc(x_1750);
lean_dec(x_1748);
x_1751 = l_Array_isEmpty___rarg(x_11);
if (x_1751 == 0)
{
lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1752 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1752, 0, x_1564);
x_1753 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1754 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1754, 0, x_1753);
lean_ctor_set(x_1754, 1, x_1752);
x_1755 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1756 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1756, 0, x_1754);
lean_ctor_set(x_1756, 1, x_1755);
x_1757 = x_11;
x_1758 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1568, x_1757);
x_1759 = x_1758;
x_1760 = l_Array_toList___rarg(x_1759);
lean_dec(x_1759);
x_1761 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1760);
x_1762 = l_Array_HasRepr___rarg___closed__1;
x_1763 = lean_string_append(x_1762, x_1761);
lean_dec(x_1761);
x_1764 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1764, 0, x_1763);
x_1765 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1765, 0, x_1764);
x_1766 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1766, 0, x_1756);
lean_ctor_set(x_1766, 1, x_1765);
x_1767 = l_Lean_Elab_Term_throwError___rarg(x_1766, x_1487, x_1750);
return x_1767;
}
else
{
lean_object* x_1768; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; uint8_t x_1800; 
lean_dec(x_1564);
lean_dec(x_11);
x_1793 = l_Lean_Elab_Term_getOptions(x_1487, x_1750);
x_1794 = lean_ctor_get(x_1793, 0);
lean_inc(x_1794);
x_1795 = lean_ctor_get(x_1793, 1);
lean_inc(x_1795);
lean_dec(x_1793);
x_1796 = l_Lean_Elab_Term_getCurrRef(x_1487, x_1795);
x_1797 = lean_ctor_get(x_1796, 0);
lean_inc(x_1797);
x_1798 = lean_ctor_get(x_1796, 1);
lean_inc(x_1798);
lean_dec(x_1796);
x_1799 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1800 = l_Lean_checkTraceOption(x_1794, x_1799);
lean_dec(x_1794);
if (x_1800 == 0)
{
lean_dec(x_1797);
x_1768 = x_1798;
goto block_1792;
}
else
{
lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; 
lean_inc(x_2);
x_1801 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1801, 0, x_2);
lean_inc(x_1487);
x_1802 = l_Lean_Elab_Term_logTrace(x_1799, x_1797, x_1801, x_1487, x_1798);
lean_dec(x_1797);
x_1803 = lean_ctor_get(x_1802, 1);
lean_inc(x_1803);
lean_dec(x_1802);
x_1768 = x_1803;
goto block_1792;
}
block_1792:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1769; 
lean_dec(x_3);
x_1769 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_1768);
lean_dec(x_12);
if (lean_obj_tag(x_1769) == 0)
{
lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; 
x_1770 = lean_ctor_get(x_1769, 1);
lean_inc(x_1770);
if (lean_is_exclusive(x_1769)) {
 lean_ctor_release(x_1769, 0);
 lean_ctor_release(x_1769, 1);
 x_1771 = x_1769;
} else {
 lean_dec_ref(x_1769);
 x_1771 = lean_box(0);
}
if (lean_is_scalar(x_1771)) {
 x_1772 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1772 = x_1771;
}
lean_ctor_set(x_1772, 0, x_2);
lean_ctor_set(x_1772, 1, x_1770);
return x_1772;
}
else
{
lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; 
lean_dec(x_2);
x_1773 = lean_ctor_get(x_1769, 0);
lean_inc(x_1773);
x_1774 = lean_ctor_get(x_1769, 1);
lean_inc(x_1774);
if (lean_is_exclusive(x_1769)) {
 lean_ctor_release(x_1769, 0);
 lean_ctor_release(x_1769, 1);
 x_1775 = x_1769;
} else {
 lean_dec_ref(x_1769);
 x_1775 = lean_box(0);
}
if (lean_is_scalar(x_1775)) {
 x_1776 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1776 = x_1775;
}
lean_ctor_set(x_1776, 0, x_1773);
lean_ctor_set(x_1776, 1, x_1774);
return x_1776;
}
}
else
{
lean_object* x_1777; lean_object* x_1778; 
x_1777 = lean_ctor_get(x_8, 0);
lean_inc(x_1777);
lean_dec(x_8);
lean_inc(x_1487);
x_1778 = l_Lean_Elab_Term_isDefEq(x_1777, x_3, x_1487, x_1768);
if (lean_obj_tag(x_1778) == 0)
{
lean_object* x_1779; lean_object* x_1780; 
x_1779 = lean_ctor_get(x_1778, 1);
lean_inc(x_1779);
lean_dec(x_1778);
x_1780 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_1779);
lean_dec(x_12);
if (lean_obj_tag(x_1780) == 0)
{
lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; 
x_1781 = lean_ctor_get(x_1780, 1);
lean_inc(x_1781);
if (lean_is_exclusive(x_1780)) {
 lean_ctor_release(x_1780, 0);
 lean_ctor_release(x_1780, 1);
 x_1782 = x_1780;
} else {
 lean_dec_ref(x_1780);
 x_1782 = lean_box(0);
}
if (lean_is_scalar(x_1782)) {
 x_1783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1783 = x_1782;
}
lean_ctor_set(x_1783, 0, x_2);
lean_ctor_set(x_1783, 1, x_1781);
return x_1783;
}
else
{
lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; 
lean_dec(x_2);
x_1784 = lean_ctor_get(x_1780, 0);
lean_inc(x_1784);
x_1785 = lean_ctor_get(x_1780, 1);
lean_inc(x_1785);
if (lean_is_exclusive(x_1780)) {
 lean_ctor_release(x_1780, 0);
 lean_ctor_release(x_1780, 1);
 x_1786 = x_1780;
} else {
 lean_dec_ref(x_1780);
 x_1786 = lean_box(0);
}
if (lean_is_scalar(x_1786)) {
 x_1787 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1787 = x_1786;
}
lean_ctor_set(x_1787, 0, x_1784);
lean_ctor_set(x_1787, 1, x_1785);
return x_1787;
}
}
else
{
lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; 
lean_dec(x_1487);
lean_dec(x_12);
lean_dec(x_2);
x_1788 = lean_ctor_get(x_1778, 0);
lean_inc(x_1788);
x_1789 = lean_ctor_get(x_1778, 1);
lean_inc(x_1789);
if (lean_is_exclusive(x_1778)) {
 lean_ctor_release(x_1778, 0);
 lean_ctor_release(x_1778, 1);
 x_1790 = x_1778;
} else {
 lean_dec_ref(x_1778);
 x_1790 = lean_box(0);
}
if (lean_is_scalar(x_1790)) {
 x_1791 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1791 = x_1790;
}
lean_ctor_set(x_1791, 0, x_1788);
lean_ctor_set(x_1791, 1, x_1789);
return x_1791;
}
}
}
}
}
else
{
lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; 
lean_dec(x_1564);
lean_dec(x_3);
x_1804 = lean_ctor_get(x_1748, 1);
lean_inc(x_1804);
lean_dec(x_1748);
x_1805 = lean_array_fget(x_7, x_10);
lean_inc(x_1487);
lean_inc(x_2);
x_1806 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1805, x_1565, x_1487, x_1804);
if (lean_obj_tag(x_1806) == 0)
{
lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; uint8_t x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; 
x_1807 = lean_ctor_get(x_1806, 0);
lean_inc(x_1807);
x_1808 = lean_ctor_get(x_1806, 1);
lean_inc(x_1808);
lean_dec(x_1806);
x_1809 = lean_unsigned_to_nat(1u);
x_1810 = lean_nat_add(x_10, x_1809);
lean_dec(x_10);
x_1811 = 1;
if (lean_is_scalar(x_1749)) {
 x_1812 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1812 = x_1749;
}
lean_ctor_set(x_1812, 0, x_6);
lean_ctor_set(x_1812, 1, x_7);
lean_ctor_set(x_1812, 2, x_8);
lean_ctor_set(x_1812, 3, x_1810);
lean_ctor_set(x_1812, 4, x_11);
lean_ctor_set(x_1812, 5, x_12);
lean_ctor_set(x_1812, 6, x_13);
lean_ctor_set_uint8(x_1812, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1812, sizeof(void*)*7 + 1, x_1811);
lean_inc(x_1807);
x_1813 = l_Lean_mkApp(x_2, x_1807);
x_1814 = lean_expr_instantiate1(x_1566, x_1807);
lean_dec(x_1807);
lean_dec(x_1566);
x_1 = x_1812;
x_2 = x_1813;
x_3 = x_1814;
x_4 = x_1487;
x_5 = x_1808;
goto _start;
}
else
{
lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; 
lean_dec(x_1749);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1816 = lean_ctor_get(x_1806, 0);
lean_inc(x_1816);
x_1817 = lean_ctor_get(x_1806, 1);
lean_inc(x_1817);
if (lean_is_exclusive(x_1806)) {
 lean_ctor_release(x_1806, 0);
 lean_ctor_release(x_1806, 1);
 x_1818 = x_1806;
} else {
 lean_dec_ref(x_1806);
 x_1818 = lean_box(0);
}
if (lean_is_scalar(x_1818)) {
 x_1819 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1819 = x_1818;
}
lean_ctor_set(x_1819, 0, x_1816);
lean_ctor_set(x_1819, 1, x_1817);
return x_1819;
}
}
}
else
{
lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; 
lean_dec(x_1749);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_1564);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_1820 = lean_ctor_get(x_1748, 0);
lean_inc(x_1820);
x_1821 = lean_ctor_get(x_1748, 1);
lean_inc(x_1821);
if (lean_is_exclusive(x_1748)) {
 lean_ctor_release(x_1748, 0);
 lean_ctor_release(x_1748, 1);
 x_1822 = x_1748;
} else {
 lean_dec_ref(x_1748);
 x_1822 = lean_box(0);
}
if (lean_is_scalar(x_1822)) {
 x_1823 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1823 = x_1822;
}
lean_ctor_set(x_1823, 0, x_1820);
lean_ctor_set(x_1823, 1, x_1821);
return x_1823;
}
}
}
case 2:
{
uint8_t x_1824; lean_object* x_1825; lean_object* x_1826; uint8_t x_1827; lean_object* x_1828; lean_object* x_1829; 
x_1824 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1825 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1825, 0, x_6);
lean_ctor_set(x_1825, 1, x_7);
lean_ctor_set(x_1825, 2, x_8);
lean_ctor_set(x_1825, 3, x_10);
lean_ctor_set(x_1825, 4, x_11);
lean_ctor_set(x_1825, 5, x_12);
lean_ctor_set(x_1825, 6, x_13);
lean_ctor_set_uint8(x_1825, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1825, sizeof(void*)*7 + 1, x_1824);
x_1826 = lean_array_get_size(x_7);
x_1827 = lean_nat_dec_lt(x_10, x_1826);
lean_dec(x_1826);
lean_inc(x_1487);
lean_inc(x_1);
x_1828 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1489, x_1487, x_1490);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1829 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1829 = lean_box(0);
}
if (lean_obj_tag(x_1828) == 0)
{
lean_object* x_1830; lean_object* x_1831; 
x_1830 = lean_ctor_get(x_1828, 1);
lean_inc(x_1830);
lean_dec(x_1828);
if (x_1827 == 0)
{
lean_dec(x_1829);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1886; 
x_1886 = l_Lean_Expr_getOptParamDefault_x3f(x_1565);
if (lean_obj_tag(x_1886) == 0)
{
lean_object* x_1887; 
x_1887 = l_Lean_Expr_getAutoParamTactic_x3f(x_1565);
if (lean_obj_tag(x_1887) == 0)
{
lean_object* x_1888; 
lean_dec(x_1825);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
x_1888 = lean_box(0);
x_1831 = x_1888;
goto block_1885;
}
else
{
lean_object* x_1889; 
lean_dec(x_1564);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1889 = lean_ctor_get(x_1887, 0);
lean_inc(x_1889);
lean_dec(x_1887);
if (lean_obj_tag(x_1889) == 4)
{
lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; 
x_1890 = lean_ctor_get(x_1889, 0);
lean_inc(x_1890);
lean_dec(x_1889);
x_1891 = l_Lean_Elab_Term_getEnv___rarg(x_1830);
x_1892 = lean_ctor_get(x_1891, 0);
lean_inc(x_1892);
x_1893 = lean_ctor_get(x_1891, 1);
lean_inc(x_1893);
lean_dec(x_1891);
x_1894 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1892, x_1890);
if (lean_obj_tag(x_1894) == 0)
{
lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; 
lean_dec(x_1825);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
lean_dec(x_2);
x_1895 = lean_ctor_get(x_1894, 0);
lean_inc(x_1895);
lean_dec(x_1894);
x_1896 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1896, 0, x_1895);
x_1897 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1897, 0, x_1896);
x_1898 = l_Lean_Elab_Term_throwError___rarg(x_1897, x_1487, x_1893);
return x_1898;
}
else
{
lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; 
x_1899 = lean_ctor_get(x_1894, 0);
lean_inc(x_1899);
lean_dec(x_1894);
x_1900 = l_Lean_Elab_Term_getCurrMacroScope(x_1487, x_1893);
x_1901 = lean_ctor_get(x_1900, 1);
lean_inc(x_1901);
lean_dec(x_1900);
x_1902 = l_Lean_Elab_Term_getMainModule___rarg(x_1901);
x_1903 = lean_ctor_get(x_1902, 1);
lean_inc(x_1903);
lean_dec(x_1902);
x_1904 = l_Lean_Syntax_getArgs(x_1899);
lean_dec(x_1899);
x_1905 = l_Array_empty___closed__1;
x_1906 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1904, x_1904, x_1568, x_1905);
lean_dec(x_1904);
x_1907 = l_Lean_nullKind___closed__2;
x_1908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1908, 0, x_1907);
lean_ctor_set(x_1908, 1, x_1906);
x_1909 = lean_array_push(x_1905, x_1908);
x_1910 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_1911 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1911, 0, x_1910);
lean_ctor_set(x_1911, 1, x_1909);
x_1912 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1913 = lean_array_push(x_1912, x_1911);
x_1914 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1915 = lean_array_push(x_1913, x_1914);
x_1916 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1917, 0, x_1916);
lean_ctor_set(x_1917, 1, x_1915);
x_1918 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_1919 = l_Lean_Expr_getAppNumArgsAux___main(x_1565, x_1568);
x_1920 = lean_nat_sub(x_1919, x_1568);
lean_dec(x_1919);
x_1921 = lean_unsigned_to_nat(1u);
x_1922 = lean_nat_sub(x_1920, x_1921);
lean_dec(x_1920);
x_1923 = l_Lean_Expr_getRevArg_x21___main(x_1565, x_1922);
lean_dec(x_1565);
if (lean_obj_tag(x_1918) == 0)
{
lean_object* x_1924; lean_object* x_1925; 
x_1924 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1924, 0, x_1917);
lean_inc(x_1487);
lean_inc(x_2);
x_1925 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1924, x_1923, x_1487, x_1903);
if (lean_obj_tag(x_1925) == 0)
{
lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; 
x_1926 = lean_ctor_get(x_1925, 0);
lean_inc(x_1926);
x_1927 = lean_ctor_get(x_1925, 1);
lean_inc(x_1927);
lean_dec(x_1925);
lean_inc(x_1926);
x_1928 = l_Lean_mkApp(x_2, x_1926);
x_1929 = lean_expr_instantiate1(x_1566, x_1926);
lean_dec(x_1926);
lean_dec(x_1566);
x_1 = x_1825;
x_2 = x_1928;
x_3 = x_1929;
x_4 = x_1487;
x_5 = x_1927;
goto _start;
}
else
{
lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; 
lean_dec(x_1825);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_2);
x_1931 = lean_ctor_get(x_1925, 0);
lean_inc(x_1931);
x_1932 = lean_ctor_get(x_1925, 1);
lean_inc(x_1932);
if (lean_is_exclusive(x_1925)) {
 lean_ctor_release(x_1925, 0);
 lean_ctor_release(x_1925, 1);
 x_1933 = x_1925;
} else {
 lean_dec_ref(x_1925);
 x_1933 = lean_box(0);
}
if (lean_is_scalar(x_1933)) {
 x_1934 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1934 = x_1933;
}
lean_ctor_set(x_1934, 0, x_1931);
lean_ctor_set(x_1934, 1, x_1932);
return x_1934;
}
}
else
{
lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; 
x_1935 = lean_ctor_get(x_1918, 0);
lean_inc(x_1935);
lean_dec(x_1918);
x_1936 = l_Lean_Syntax_replaceInfo___main(x_1935, x_1917);
x_1937 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1937, 0, x_1936);
lean_inc(x_1487);
lean_inc(x_2);
x_1938 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1937, x_1923, x_1487, x_1903);
if (lean_obj_tag(x_1938) == 0)
{
lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; 
x_1939 = lean_ctor_get(x_1938, 0);
lean_inc(x_1939);
x_1940 = lean_ctor_get(x_1938, 1);
lean_inc(x_1940);
lean_dec(x_1938);
lean_inc(x_1939);
x_1941 = l_Lean_mkApp(x_2, x_1939);
x_1942 = lean_expr_instantiate1(x_1566, x_1939);
lean_dec(x_1939);
lean_dec(x_1566);
x_1 = x_1825;
x_2 = x_1941;
x_3 = x_1942;
x_4 = x_1487;
x_5 = x_1940;
goto _start;
}
else
{
lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; 
lean_dec(x_1825);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_2);
x_1944 = lean_ctor_get(x_1938, 0);
lean_inc(x_1944);
x_1945 = lean_ctor_get(x_1938, 1);
lean_inc(x_1945);
if (lean_is_exclusive(x_1938)) {
 lean_ctor_release(x_1938, 0);
 lean_ctor_release(x_1938, 1);
 x_1946 = x_1938;
} else {
 lean_dec_ref(x_1938);
 x_1946 = lean_box(0);
}
if (lean_is_scalar(x_1946)) {
 x_1947 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1947 = x_1946;
}
lean_ctor_set(x_1947, 0, x_1944);
lean_ctor_set(x_1947, 1, x_1945);
return x_1947;
}
}
}
}
else
{
lean_object* x_1948; lean_object* x_1949; 
lean_dec(x_1889);
lean_dec(x_1825);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
lean_dec(x_2);
x_1948 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1949 = l_Lean_Elab_Term_throwError___rarg(x_1948, x_1487, x_1830);
return x_1949;
}
}
}
else
{
lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; 
lean_dec(x_1565);
lean_dec(x_1564);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1950 = lean_ctor_get(x_1886, 0);
lean_inc(x_1950);
lean_dec(x_1886);
lean_inc(x_1950);
x_1951 = l_Lean_mkApp(x_2, x_1950);
x_1952 = lean_expr_instantiate1(x_1566, x_1950);
lean_dec(x_1950);
lean_dec(x_1566);
x_1 = x_1825;
x_2 = x_1951;
x_3 = x_1952;
x_4 = x_1487;
x_5 = x_1830;
goto _start;
}
}
else
{
lean_object* x_1954; 
lean_dec(x_1825);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
x_1954 = lean_box(0);
x_1831 = x_1954;
goto block_1885;
}
}
else
{
lean_object* x_1955; lean_object* x_1956; 
lean_dec(x_1825);
lean_dec(x_1564);
lean_dec(x_3);
x_1955 = lean_array_fget(x_7, x_10);
lean_inc(x_1487);
lean_inc(x_2);
x_1956 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1955, x_1565, x_1487, x_1830);
if (lean_obj_tag(x_1956) == 0)
{
lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; 
x_1957 = lean_ctor_get(x_1956, 0);
lean_inc(x_1957);
x_1958 = lean_ctor_get(x_1956, 1);
lean_inc(x_1958);
lean_dec(x_1956);
x_1959 = lean_unsigned_to_nat(1u);
x_1960 = lean_nat_add(x_10, x_1959);
lean_dec(x_10);
if (lean_is_scalar(x_1829)) {
 x_1961 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1961 = x_1829;
}
lean_ctor_set(x_1961, 0, x_6);
lean_ctor_set(x_1961, 1, x_7);
lean_ctor_set(x_1961, 2, x_8);
lean_ctor_set(x_1961, 3, x_1960);
lean_ctor_set(x_1961, 4, x_11);
lean_ctor_set(x_1961, 5, x_12);
lean_ctor_set(x_1961, 6, x_13);
lean_ctor_set_uint8(x_1961, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1961, sizeof(void*)*7 + 1, x_1824);
lean_inc(x_1957);
x_1962 = l_Lean_mkApp(x_2, x_1957);
x_1963 = lean_expr_instantiate1(x_1566, x_1957);
lean_dec(x_1957);
lean_dec(x_1566);
x_1 = x_1961;
x_2 = x_1962;
x_3 = x_1963;
x_4 = x_1487;
x_5 = x_1958;
goto _start;
}
else
{
lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; 
lean_dec(x_1829);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1965 = lean_ctor_get(x_1956, 0);
lean_inc(x_1965);
x_1966 = lean_ctor_get(x_1956, 1);
lean_inc(x_1966);
if (lean_is_exclusive(x_1956)) {
 lean_ctor_release(x_1956, 0);
 lean_ctor_release(x_1956, 1);
 x_1967 = x_1956;
} else {
 lean_dec_ref(x_1956);
 x_1967 = lean_box(0);
}
if (lean_is_scalar(x_1967)) {
 x_1968 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1968 = x_1967;
}
lean_ctor_set(x_1968, 0, x_1965);
lean_ctor_set(x_1968, 1, x_1966);
return x_1968;
}
}
block_1885:
{
uint8_t x_1832; 
lean_dec(x_1831);
x_1832 = l_Array_isEmpty___rarg(x_11);
if (x_1832 == 0)
{
lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1833 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1833, 0, x_1564);
x_1834 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1835 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1835, 0, x_1834);
lean_ctor_set(x_1835, 1, x_1833);
x_1836 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1837 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1837, 0, x_1835);
lean_ctor_set(x_1837, 1, x_1836);
x_1838 = x_11;
x_1839 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1568, x_1838);
x_1840 = x_1839;
x_1841 = l_Array_toList___rarg(x_1840);
lean_dec(x_1840);
x_1842 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1841);
x_1843 = l_Array_HasRepr___rarg___closed__1;
x_1844 = lean_string_append(x_1843, x_1842);
lean_dec(x_1842);
x_1845 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1845, 0, x_1844);
x_1846 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1846, 0, x_1845);
x_1847 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1847, 0, x_1837);
lean_ctor_set(x_1847, 1, x_1846);
x_1848 = l_Lean_Elab_Term_throwError___rarg(x_1847, x_1487, x_1830);
return x_1848;
}
else
{
lean_object* x_1849; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; uint8_t x_1881; 
lean_dec(x_1564);
lean_dec(x_11);
x_1874 = l_Lean_Elab_Term_getOptions(x_1487, x_1830);
x_1875 = lean_ctor_get(x_1874, 0);
lean_inc(x_1875);
x_1876 = lean_ctor_get(x_1874, 1);
lean_inc(x_1876);
lean_dec(x_1874);
x_1877 = l_Lean_Elab_Term_getCurrRef(x_1487, x_1876);
x_1878 = lean_ctor_get(x_1877, 0);
lean_inc(x_1878);
x_1879 = lean_ctor_get(x_1877, 1);
lean_inc(x_1879);
lean_dec(x_1877);
x_1880 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1881 = l_Lean_checkTraceOption(x_1875, x_1880);
lean_dec(x_1875);
if (x_1881 == 0)
{
lean_dec(x_1878);
x_1849 = x_1879;
goto block_1873;
}
else
{
lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; 
lean_inc(x_2);
x_1882 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1882, 0, x_2);
lean_inc(x_1487);
x_1883 = l_Lean_Elab_Term_logTrace(x_1880, x_1878, x_1882, x_1487, x_1879);
lean_dec(x_1878);
x_1884 = lean_ctor_get(x_1883, 1);
lean_inc(x_1884);
lean_dec(x_1883);
x_1849 = x_1884;
goto block_1873;
}
block_1873:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1850; 
lean_dec(x_3);
x_1850 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_1849);
lean_dec(x_12);
if (lean_obj_tag(x_1850) == 0)
{
lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; 
x_1851 = lean_ctor_get(x_1850, 1);
lean_inc(x_1851);
if (lean_is_exclusive(x_1850)) {
 lean_ctor_release(x_1850, 0);
 lean_ctor_release(x_1850, 1);
 x_1852 = x_1850;
} else {
 lean_dec_ref(x_1850);
 x_1852 = lean_box(0);
}
if (lean_is_scalar(x_1852)) {
 x_1853 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1853 = x_1852;
}
lean_ctor_set(x_1853, 0, x_2);
lean_ctor_set(x_1853, 1, x_1851);
return x_1853;
}
else
{
lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; 
lean_dec(x_2);
x_1854 = lean_ctor_get(x_1850, 0);
lean_inc(x_1854);
x_1855 = lean_ctor_get(x_1850, 1);
lean_inc(x_1855);
if (lean_is_exclusive(x_1850)) {
 lean_ctor_release(x_1850, 0);
 lean_ctor_release(x_1850, 1);
 x_1856 = x_1850;
} else {
 lean_dec_ref(x_1850);
 x_1856 = lean_box(0);
}
if (lean_is_scalar(x_1856)) {
 x_1857 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1857 = x_1856;
}
lean_ctor_set(x_1857, 0, x_1854);
lean_ctor_set(x_1857, 1, x_1855);
return x_1857;
}
}
else
{
lean_object* x_1858; lean_object* x_1859; 
x_1858 = lean_ctor_get(x_8, 0);
lean_inc(x_1858);
lean_dec(x_8);
lean_inc(x_1487);
x_1859 = l_Lean_Elab_Term_isDefEq(x_1858, x_3, x_1487, x_1849);
if (lean_obj_tag(x_1859) == 0)
{
lean_object* x_1860; lean_object* x_1861; 
x_1860 = lean_ctor_get(x_1859, 1);
lean_inc(x_1860);
lean_dec(x_1859);
x_1861 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_1860);
lean_dec(x_12);
if (lean_obj_tag(x_1861) == 0)
{
lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; 
x_1862 = lean_ctor_get(x_1861, 1);
lean_inc(x_1862);
if (lean_is_exclusive(x_1861)) {
 lean_ctor_release(x_1861, 0);
 lean_ctor_release(x_1861, 1);
 x_1863 = x_1861;
} else {
 lean_dec_ref(x_1861);
 x_1863 = lean_box(0);
}
if (lean_is_scalar(x_1863)) {
 x_1864 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1864 = x_1863;
}
lean_ctor_set(x_1864, 0, x_2);
lean_ctor_set(x_1864, 1, x_1862);
return x_1864;
}
else
{
lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; 
lean_dec(x_2);
x_1865 = lean_ctor_get(x_1861, 0);
lean_inc(x_1865);
x_1866 = lean_ctor_get(x_1861, 1);
lean_inc(x_1866);
if (lean_is_exclusive(x_1861)) {
 lean_ctor_release(x_1861, 0);
 lean_ctor_release(x_1861, 1);
 x_1867 = x_1861;
} else {
 lean_dec_ref(x_1861);
 x_1867 = lean_box(0);
}
if (lean_is_scalar(x_1867)) {
 x_1868 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1868 = x_1867;
}
lean_ctor_set(x_1868, 0, x_1865);
lean_ctor_set(x_1868, 1, x_1866);
return x_1868;
}
}
else
{
lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; 
lean_dec(x_1487);
lean_dec(x_12);
lean_dec(x_2);
x_1869 = lean_ctor_get(x_1859, 0);
lean_inc(x_1869);
x_1870 = lean_ctor_get(x_1859, 1);
lean_inc(x_1870);
if (lean_is_exclusive(x_1859)) {
 lean_ctor_release(x_1859, 0);
 lean_ctor_release(x_1859, 1);
 x_1871 = x_1859;
} else {
 lean_dec_ref(x_1859);
 x_1871 = lean_box(0);
}
if (lean_is_scalar(x_1871)) {
 x_1872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1872 = x_1871;
}
lean_ctor_set(x_1872, 0, x_1869);
lean_ctor_set(x_1872, 1, x_1870);
return x_1872;
}
}
}
}
}
}
else
{
lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; 
lean_dec(x_1829);
lean_dec(x_1825);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_1564);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_1969 = lean_ctor_get(x_1828, 0);
lean_inc(x_1969);
x_1970 = lean_ctor_get(x_1828, 1);
lean_inc(x_1970);
if (lean_is_exclusive(x_1828)) {
 lean_ctor_release(x_1828, 0);
 lean_ctor_release(x_1828, 1);
 x_1971 = x_1828;
} else {
 lean_dec_ref(x_1828);
 x_1971 = lean_box(0);
}
if (lean_is_scalar(x_1971)) {
 x_1972 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1972 = x_1971;
}
lean_ctor_set(x_1972, 0, x_1969);
lean_ctor_set(x_1972, 1, x_1970);
return x_1972;
}
}
case 3:
{
if (x_9 == 0)
{
lean_object* x_1973; lean_object* x_1974; uint8_t x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; 
lean_dec(x_1564);
lean_dec(x_1489);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1973 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1973 = lean_box(0);
}
x_1974 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1974, 0, x_1565);
x_1975 = 1;
x_1976 = lean_box(0);
lean_inc(x_1487);
x_1977 = l_Lean_Elab_Term_mkFreshExprMVar(x_1974, x_1975, x_1976, x_1487, x_1490);
x_1978 = lean_ctor_get(x_1977, 0);
lean_inc(x_1978);
x_1979 = lean_ctor_get(x_1977, 1);
lean_inc(x_1979);
lean_dec(x_1977);
x_1980 = l_Lean_Expr_mvarId_x21(x_1978);
x_1981 = lean_array_push(x_12, x_1980);
if (lean_is_scalar(x_1973)) {
 x_1982 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1982 = x_1973;
}
lean_ctor_set(x_1982, 0, x_6);
lean_ctor_set(x_1982, 1, x_7);
lean_ctor_set(x_1982, 2, x_8);
lean_ctor_set(x_1982, 3, x_10);
lean_ctor_set(x_1982, 4, x_11);
lean_ctor_set(x_1982, 5, x_1981);
lean_ctor_set(x_1982, 6, x_13);
lean_ctor_set_uint8(x_1982, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1982, sizeof(void*)*7 + 1, x_1473);
lean_inc(x_1978);
x_1983 = l_Lean_mkApp(x_2, x_1978);
x_1984 = lean_expr_instantiate1(x_1566, x_1978);
lean_dec(x_1978);
lean_dec(x_1566);
x_1 = x_1982;
x_2 = x_1983;
x_3 = x_1984;
x_4 = x_1487;
x_5 = x_1979;
goto _start;
}
else
{
uint8_t x_1986; 
x_1986 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_1986 == 0)
{
lean_object* x_1987; uint8_t x_1988; lean_object* x_1989; lean_object* x_1990; 
x_1987 = lean_array_get_size(x_7);
x_1988 = lean_nat_dec_lt(x_10, x_1987);
lean_dec(x_1987);
lean_inc(x_1487);
lean_inc(x_1);
x_1989 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1489, x_1487, x_1490);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1990 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1990 = lean_box(0);
}
if (lean_obj_tag(x_1989) == 0)
{
if (x_1988 == 0)
{
lean_object* x_1991; uint8_t x_1992; 
lean_dec(x_1990);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_1991 = lean_ctor_get(x_1989, 1);
lean_inc(x_1991);
lean_dec(x_1989);
x_1992 = l_Array_isEmpty___rarg(x_11);
if (x_1992 == 0)
{
lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1993 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1993, 0, x_1564);
x_1994 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1995 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1995, 0, x_1994);
lean_ctor_set(x_1995, 1, x_1993);
x_1996 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1997 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1997, 0, x_1995);
lean_ctor_set(x_1997, 1, x_1996);
x_1998 = x_11;
x_1999 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1568, x_1998);
x_2000 = x_1999;
x_2001 = l_Array_toList___rarg(x_2000);
lean_dec(x_2000);
x_2002 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2001);
x_2003 = l_Array_HasRepr___rarg___closed__1;
x_2004 = lean_string_append(x_2003, x_2002);
lean_dec(x_2002);
x_2005 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2005, 0, x_2004);
x_2006 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2006, 0, x_2005);
x_2007 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2007, 0, x_1997);
lean_ctor_set(x_2007, 1, x_2006);
x_2008 = l_Lean_Elab_Term_throwError___rarg(x_2007, x_1487, x_1991);
return x_2008;
}
else
{
lean_object* x_2009; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; uint8_t x_2041; 
lean_dec(x_1564);
lean_dec(x_11);
x_2034 = l_Lean_Elab_Term_getOptions(x_1487, x_1991);
x_2035 = lean_ctor_get(x_2034, 0);
lean_inc(x_2035);
x_2036 = lean_ctor_get(x_2034, 1);
lean_inc(x_2036);
lean_dec(x_2034);
x_2037 = l_Lean_Elab_Term_getCurrRef(x_1487, x_2036);
x_2038 = lean_ctor_get(x_2037, 0);
lean_inc(x_2038);
x_2039 = lean_ctor_get(x_2037, 1);
lean_inc(x_2039);
lean_dec(x_2037);
x_2040 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2041 = l_Lean_checkTraceOption(x_2035, x_2040);
lean_dec(x_2035);
if (x_2041 == 0)
{
lean_dec(x_2038);
x_2009 = x_2039;
goto block_2033;
}
else
{
lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; 
lean_inc(x_2);
x_2042 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2042, 0, x_2);
lean_inc(x_1487);
x_2043 = l_Lean_Elab_Term_logTrace(x_2040, x_2038, x_2042, x_1487, x_2039);
lean_dec(x_2038);
x_2044 = lean_ctor_get(x_2043, 1);
lean_inc(x_2044);
lean_dec(x_2043);
x_2009 = x_2044;
goto block_2033;
}
block_2033:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_2010; 
lean_dec(x_3);
x_2010 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_2009);
lean_dec(x_12);
if (lean_obj_tag(x_2010) == 0)
{
lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; 
x_2011 = lean_ctor_get(x_2010, 1);
lean_inc(x_2011);
if (lean_is_exclusive(x_2010)) {
 lean_ctor_release(x_2010, 0);
 lean_ctor_release(x_2010, 1);
 x_2012 = x_2010;
} else {
 lean_dec_ref(x_2010);
 x_2012 = lean_box(0);
}
if (lean_is_scalar(x_2012)) {
 x_2013 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2013 = x_2012;
}
lean_ctor_set(x_2013, 0, x_2);
lean_ctor_set(x_2013, 1, x_2011);
return x_2013;
}
else
{
lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; 
lean_dec(x_2);
x_2014 = lean_ctor_get(x_2010, 0);
lean_inc(x_2014);
x_2015 = lean_ctor_get(x_2010, 1);
lean_inc(x_2015);
if (lean_is_exclusive(x_2010)) {
 lean_ctor_release(x_2010, 0);
 lean_ctor_release(x_2010, 1);
 x_2016 = x_2010;
} else {
 lean_dec_ref(x_2010);
 x_2016 = lean_box(0);
}
if (lean_is_scalar(x_2016)) {
 x_2017 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2017 = x_2016;
}
lean_ctor_set(x_2017, 0, x_2014);
lean_ctor_set(x_2017, 1, x_2015);
return x_2017;
}
}
else
{
lean_object* x_2018; lean_object* x_2019; 
x_2018 = lean_ctor_get(x_8, 0);
lean_inc(x_2018);
lean_dec(x_8);
lean_inc(x_1487);
x_2019 = l_Lean_Elab_Term_isDefEq(x_2018, x_3, x_1487, x_2009);
if (lean_obj_tag(x_2019) == 0)
{
lean_object* x_2020; lean_object* x_2021; 
x_2020 = lean_ctor_get(x_2019, 1);
lean_inc(x_2020);
lean_dec(x_2019);
x_2021 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_2020);
lean_dec(x_12);
if (lean_obj_tag(x_2021) == 0)
{
lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; 
x_2022 = lean_ctor_get(x_2021, 1);
lean_inc(x_2022);
if (lean_is_exclusive(x_2021)) {
 lean_ctor_release(x_2021, 0);
 lean_ctor_release(x_2021, 1);
 x_2023 = x_2021;
} else {
 lean_dec_ref(x_2021);
 x_2023 = lean_box(0);
}
if (lean_is_scalar(x_2023)) {
 x_2024 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2024 = x_2023;
}
lean_ctor_set(x_2024, 0, x_2);
lean_ctor_set(x_2024, 1, x_2022);
return x_2024;
}
else
{
lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; 
lean_dec(x_2);
x_2025 = lean_ctor_get(x_2021, 0);
lean_inc(x_2025);
x_2026 = lean_ctor_get(x_2021, 1);
lean_inc(x_2026);
if (lean_is_exclusive(x_2021)) {
 lean_ctor_release(x_2021, 0);
 lean_ctor_release(x_2021, 1);
 x_2027 = x_2021;
} else {
 lean_dec_ref(x_2021);
 x_2027 = lean_box(0);
}
if (lean_is_scalar(x_2027)) {
 x_2028 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2028 = x_2027;
}
lean_ctor_set(x_2028, 0, x_2025);
lean_ctor_set(x_2028, 1, x_2026);
return x_2028;
}
}
else
{
lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; 
lean_dec(x_1487);
lean_dec(x_12);
lean_dec(x_2);
x_2029 = lean_ctor_get(x_2019, 0);
lean_inc(x_2029);
x_2030 = lean_ctor_get(x_2019, 1);
lean_inc(x_2030);
if (lean_is_exclusive(x_2019)) {
 lean_ctor_release(x_2019, 0);
 lean_ctor_release(x_2019, 1);
 x_2031 = x_2019;
} else {
 lean_dec_ref(x_2019);
 x_2031 = lean_box(0);
}
if (lean_is_scalar(x_2031)) {
 x_2032 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2032 = x_2031;
}
lean_ctor_set(x_2032, 0, x_2029);
lean_ctor_set(x_2032, 1, x_2030);
return x_2032;
}
}
}
}
}
else
{
lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; 
lean_dec(x_1564);
lean_dec(x_3);
x_2045 = lean_ctor_get(x_1989, 1);
lean_inc(x_2045);
lean_dec(x_1989);
x_2046 = lean_array_fget(x_7, x_10);
lean_inc(x_1487);
lean_inc(x_2);
x_2047 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2046, x_1565, x_1487, x_2045);
if (lean_obj_tag(x_2047) == 0)
{
lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; uint8_t x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; 
x_2048 = lean_ctor_get(x_2047, 0);
lean_inc(x_2048);
x_2049 = lean_ctor_get(x_2047, 1);
lean_inc(x_2049);
lean_dec(x_2047);
x_2050 = lean_unsigned_to_nat(1u);
x_2051 = lean_nat_add(x_10, x_2050);
lean_dec(x_10);
x_2052 = 1;
if (lean_is_scalar(x_1990)) {
 x_2053 = lean_alloc_ctor(0, 7, 2);
} else {
 x_2053 = x_1990;
}
lean_ctor_set(x_2053, 0, x_6);
lean_ctor_set(x_2053, 1, x_7);
lean_ctor_set(x_2053, 2, x_8);
lean_ctor_set(x_2053, 3, x_2051);
lean_ctor_set(x_2053, 4, x_11);
lean_ctor_set(x_2053, 5, x_12);
lean_ctor_set(x_2053, 6, x_13);
lean_ctor_set_uint8(x_2053, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2053, sizeof(void*)*7 + 1, x_2052);
lean_inc(x_2048);
x_2054 = l_Lean_mkApp(x_2, x_2048);
x_2055 = lean_expr_instantiate1(x_1566, x_2048);
lean_dec(x_2048);
lean_dec(x_1566);
x_1 = x_2053;
x_2 = x_2054;
x_3 = x_2055;
x_4 = x_1487;
x_5 = x_2049;
goto _start;
}
else
{
lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; 
lean_dec(x_1990);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_2057 = lean_ctor_get(x_2047, 0);
lean_inc(x_2057);
x_2058 = lean_ctor_get(x_2047, 1);
lean_inc(x_2058);
if (lean_is_exclusive(x_2047)) {
 lean_ctor_release(x_2047, 0);
 lean_ctor_release(x_2047, 1);
 x_2059 = x_2047;
} else {
 lean_dec_ref(x_2047);
 x_2059 = lean_box(0);
}
if (lean_is_scalar(x_2059)) {
 x_2060 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2060 = x_2059;
}
lean_ctor_set(x_2060, 0, x_2057);
lean_ctor_set(x_2060, 1, x_2058);
return x_2060;
}
}
}
else
{
lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; 
lean_dec(x_1990);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_1564);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_2061 = lean_ctor_get(x_1989, 0);
lean_inc(x_2061);
x_2062 = lean_ctor_get(x_1989, 1);
lean_inc(x_2062);
if (lean_is_exclusive(x_1989)) {
 lean_ctor_release(x_1989, 0);
 lean_ctor_release(x_1989, 1);
 x_2063 = x_1989;
} else {
 lean_dec_ref(x_1989);
 x_2063 = lean_box(0);
}
if (lean_is_scalar(x_2063)) {
 x_2064 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2064 = x_2063;
}
lean_ctor_set(x_2064, 0, x_2061);
lean_ctor_set(x_2064, 1, x_2062);
return x_2064;
}
}
else
{
lean_object* x_2065; lean_object* x_2066; uint8_t x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; 
lean_dec(x_1564);
lean_dec(x_1489);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_2065 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2065 = lean_box(0);
}
x_2066 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2066, 0, x_1565);
x_2067 = 1;
x_2068 = lean_box(0);
lean_inc(x_1487);
x_2069 = l_Lean_Elab_Term_mkFreshExprMVar(x_2066, x_2067, x_2068, x_1487, x_1490);
x_2070 = lean_ctor_get(x_2069, 0);
lean_inc(x_2070);
x_2071 = lean_ctor_get(x_2069, 1);
lean_inc(x_2071);
lean_dec(x_2069);
x_2072 = lean_unsigned_to_nat(1u);
x_2073 = lean_nat_add(x_10, x_2072);
lean_dec(x_10);
x_2074 = l_Lean_Expr_mvarId_x21(x_2070);
x_2075 = lean_array_push(x_12, x_2074);
if (lean_is_scalar(x_2065)) {
 x_2076 = lean_alloc_ctor(0, 7, 2);
} else {
 x_2076 = x_2065;
}
lean_ctor_set(x_2076, 0, x_6);
lean_ctor_set(x_2076, 1, x_7);
lean_ctor_set(x_2076, 2, x_8);
lean_ctor_set(x_2076, 3, x_2073);
lean_ctor_set(x_2076, 4, x_11);
lean_ctor_set(x_2076, 5, x_2075);
lean_ctor_set(x_2076, 6, x_13);
lean_ctor_set_uint8(x_2076, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2076, sizeof(void*)*7 + 1, x_1473);
lean_inc(x_2070);
x_2077 = l_Lean_mkApp(x_2, x_2070);
x_2078 = lean_expr_instantiate1(x_1566, x_2070);
lean_dec(x_2070);
lean_dec(x_1566);
x_1 = x_2076;
x_2 = x_2077;
x_3 = x_2078;
x_4 = x_1487;
x_5 = x_2071;
goto _start;
}
}
}
default: 
{
uint8_t x_2080; lean_object* x_2081; lean_object* x_2082; uint8_t x_2083; lean_object* x_2084; lean_object* x_2085; 
x_2080 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2081 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_2081, 0, x_6);
lean_ctor_set(x_2081, 1, x_7);
lean_ctor_set(x_2081, 2, x_8);
lean_ctor_set(x_2081, 3, x_10);
lean_ctor_set(x_2081, 4, x_11);
lean_ctor_set(x_2081, 5, x_12);
lean_ctor_set(x_2081, 6, x_13);
lean_ctor_set_uint8(x_2081, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2081, sizeof(void*)*7 + 1, x_2080);
x_2082 = lean_array_get_size(x_7);
x_2083 = lean_nat_dec_lt(x_10, x_2082);
lean_dec(x_2082);
lean_inc(x_1487);
lean_inc(x_1);
x_2084 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1489, x_1487, x_1490);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_2085 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2085 = lean_box(0);
}
if (lean_obj_tag(x_2084) == 0)
{
lean_object* x_2086; lean_object* x_2087; 
x_2086 = lean_ctor_get(x_2084, 1);
lean_inc(x_2086);
lean_dec(x_2084);
if (x_2083 == 0)
{
lean_dec(x_2085);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_2142; 
x_2142 = l_Lean_Expr_getOptParamDefault_x3f(x_1565);
if (lean_obj_tag(x_2142) == 0)
{
lean_object* x_2143; 
x_2143 = l_Lean_Expr_getAutoParamTactic_x3f(x_1565);
if (lean_obj_tag(x_2143) == 0)
{
lean_object* x_2144; 
lean_dec(x_2081);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
x_2144 = lean_box(0);
x_2087 = x_2144;
goto block_2141;
}
else
{
lean_object* x_2145; 
lean_dec(x_1564);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_2145 = lean_ctor_get(x_2143, 0);
lean_inc(x_2145);
lean_dec(x_2143);
if (lean_obj_tag(x_2145) == 4)
{
lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; 
x_2146 = lean_ctor_get(x_2145, 0);
lean_inc(x_2146);
lean_dec(x_2145);
x_2147 = l_Lean_Elab_Term_getEnv___rarg(x_2086);
x_2148 = lean_ctor_get(x_2147, 0);
lean_inc(x_2148);
x_2149 = lean_ctor_get(x_2147, 1);
lean_inc(x_2149);
lean_dec(x_2147);
x_2150 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_2148, x_2146);
if (lean_obj_tag(x_2150) == 0)
{
lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; 
lean_dec(x_2081);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
lean_dec(x_2);
x_2151 = lean_ctor_get(x_2150, 0);
lean_inc(x_2151);
lean_dec(x_2150);
x_2152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2152, 0, x_2151);
x_2153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2153, 0, x_2152);
x_2154 = l_Lean_Elab_Term_throwError___rarg(x_2153, x_1487, x_2149);
return x_2154;
}
else
{
lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; 
x_2155 = lean_ctor_get(x_2150, 0);
lean_inc(x_2155);
lean_dec(x_2150);
x_2156 = l_Lean_Elab_Term_getCurrMacroScope(x_1487, x_2149);
x_2157 = lean_ctor_get(x_2156, 1);
lean_inc(x_2157);
lean_dec(x_2156);
x_2158 = l_Lean_Elab_Term_getMainModule___rarg(x_2157);
x_2159 = lean_ctor_get(x_2158, 1);
lean_inc(x_2159);
lean_dec(x_2158);
x_2160 = l_Lean_Syntax_getArgs(x_2155);
lean_dec(x_2155);
x_2161 = l_Array_empty___closed__1;
x_2162 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2160, x_2160, x_1568, x_2161);
lean_dec(x_2160);
x_2163 = l_Lean_nullKind___closed__2;
x_2164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2164, 0, x_2163);
lean_ctor_set(x_2164, 1, x_2162);
x_2165 = lean_array_push(x_2161, x_2164);
x_2166 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_2167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2167, 0, x_2166);
lean_ctor_set(x_2167, 1, x_2165);
x_2168 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_2169 = lean_array_push(x_2168, x_2167);
x_2170 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_2171 = lean_array_push(x_2169, x_2170);
x_2172 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_2173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2173, 0, x_2172);
lean_ctor_set(x_2173, 1, x_2171);
x_2174 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_2175 = l_Lean_Expr_getAppNumArgsAux___main(x_1565, x_1568);
x_2176 = lean_nat_sub(x_2175, x_1568);
lean_dec(x_2175);
x_2177 = lean_unsigned_to_nat(1u);
x_2178 = lean_nat_sub(x_2176, x_2177);
lean_dec(x_2176);
x_2179 = l_Lean_Expr_getRevArg_x21___main(x_1565, x_2178);
lean_dec(x_1565);
if (lean_obj_tag(x_2174) == 0)
{
lean_object* x_2180; lean_object* x_2181; 
x_2180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2180, 0, x_2173);
lean_inc(x_1487);
lean_inc(x_2);
x_2181 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2180, x_2179, x_1487, x_2159);
if (lean_obj_tag(x_2181) == 0)
{
lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; 
x_2182 = lean_ctor_get(x_2181, 0);
lean_inc(x_2182);
x_2183 = lean_ctor_get(x_2181, 1);
lean_inc(x_2183);
lean_dec(x_2181);
lean_inc(x_2182);
x_2184 = l_Lean_mkApp(x_2, x_2182);
x_2185 = lean_expr_instantiate1(x_1566, x_2182);
lean_dec(x_2182);
lean_dec(x_1566);
x_1 = x_2081;
x_2 = x_2184;
x_3 = x_2185;
x_4 = x_1487;
x_5 = x_2183;
goto _start;
}
else
{
lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; 
lean_dec(x_2081);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_2);
x_2187 = lean_ctor_get(x_2181, 0);
lean_inc(x_2187);
x_2188 = lean_ctor_get(x_2181, 1);
lean_inc(x_2188);
if (lean_is_exclusive(x_2181)) {
 lean_ctor_release(x_2181, 0);
 lean_ctor_release(x_2181, 1);
 x_2189 = x_2181;
} else {
 lean_dec_ref(x_2181);
 x_2189 = lean_box(0);
}
if (lean_is_scalar(x_2189)) {
 x_2190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2190 = x_2189;
}
lean_ctor_set(x_2190, 0, x_2187);
lean_ctor_set(x_2190, 1, x_2188);
return x_2190;
}
}
else
{
lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; 
x_2191 = lean_ctor_get(x_2174, 0);
lean_inc(x_2191);
lean_dec(x_2174);
x_2192 = l_Lean_Syntax_replaceInfo___main(x_2191, x_2173);
x_2193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2193, 0, x_2192);
lean_inc(x_1487);
lean_inc(x_2);
x_2194 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2193, x_2179, x_1487, x_2159);
if (lean_obj_tag(x_2194) == 0)
{
lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; 
x_2195 = lean_ctor_get(x_2194, 0);
lean_inc(x_2195);
x_2196 = lean_ctor_get(x_2194, 1);
lean_inc(x_2196);
lean_dec(x_2194);
lean_inc(x_2195);
x_2197 = l_Lean_mkApp(x_2, x_2195);
x_2198 = lean_expr_instantiate1(x_1566, x_2195);
lean_dec(x_2195);
lean_dec(x_1566);
x_1 = x_2081;
x_2 = x_2197;
x_3 = x_2198;
x_4 = x_1487;
x_5 = x_2196;
goto _start;
}
else
{
lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; 
lean_dec(x_2081);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_2);
x_2200 = lean_ctor_get(x_2194, 0);
lean_inc(x_2200);
x_2201 = lean_ctor_get(x_2194, 1);
lean_inc(x_2201);
if (lean_is_exclusive(x_2194)) {
 lean_ctor_release(x_2194, 0);
 lean_ctor_release(x_2194, 1);
 x_2202 = x_2194;
} else {
 lean_dec_ref(x_2194);
 x_2202 = lean_box(0);
}
if (lean_is_scalar(x_2202)) {
 x_2203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2203 = x_2202;
}
lean_ctor_set(x_2203, 0, x_2200);
lean_ctor_set(x_2203, 1, x_2201);
return x_2203;
}
}
}
}
else
{
lean_object* x_2204; lean_object* x_2205; 
lean_dec(x_2145);
lean_dec(x_2081);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
lean_dec(x_2);
x_2204 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_2205 = l_Lean_Elab_Term_throwError___rarg(x_2204, x_1487, x_2086);
return x_2205;
}
}
}
else
{
lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; 
lean_dec(x_1565);
lean_dec(x_1564);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_2206 = lean_ctor_get(x_2142, 0);
lean_inc(x_2206);
lean_dec(x_2142);
lean_inc(x_2206);
x_2207 = l_Lean_mkApp(x_2, x_2206);
x_2208 = lean_expr_instantiate1(x_1566, x_2206);
lean_dec(x_2206);
lean_dec(x_1566);
x_1 = x_2081;
x_2 = x_2207;
x_3 = x_2208;
x_4 = x_1487;
x_5 = x_2086;
goto _start;
}
}
else
{
lean_object* x_2210; 
lean_dec(x_2081);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_6);
x_2210 = lean_box(0);
x_2087 = x_2210;
goto block_2141;
}
}
else
{
lean_object* x_2211; lean_object* x_2212; 
lean_dec(x_2081);
lean_dec(x_1564);
lean_dec(x_3);
x_2211 = lean_array_fget(x_7, x_10);
lean_inc(x_1487);
lean_inc(x_2);
x_2212 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2211, x_1565, x_1487, x_2086);
if (lean_obj_tag(x_2212) == 0)
{
lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; 
x_2213 = lean_ctor_get(x_2212, 0);
lean_inc(x_2213);
x_2214 = lean_ctor_get(x_2212, 1);
lean_inc(x_2214);
lean_dec(x_2212);
x_2215 = lean_unsigned_to_nat(1u);
x_2216 = lean_nat_add(x_10, x_2215);
lean_dec(x_10);
if (lean_is_scalar(x_2085)) {
 x_2217 = lean_alloc_ctor(0, 7, 2);
} else {
 x_2217 = x_2085;
}
lean_ctor_set(x_2217, 0, x_6);
lean_ctor_set(x_2217, 1, x_7);
lean_ctor_set(x_2217, 2, x_8);
lean_ctor_set(x_2217, 3, x_2216);
lean_ctor_set(x_2217, 4, x_11);
lean_ctor_set(x_2217, 5, x_12);
lean_ctor_set(x_2217, 6, x_13);
lean_ctor_set_uint8(x_2217, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2217, sizeof(void*)*7 + 1, x_2080);
lean_inc(x_2213);
x_2218 = l_Lean_mkApp(x_2, x_2213);
x_2219 = lean_expr_instantiate1(x_1566, x_2213);
lean_dec(x_2213);
lean_dec(x_1566);
x_1 = x_2217;
x_2 = x_2218;
x_3 = x_2219;
x_4 = x_1487;
x_5 = x_2214;
goto _start;
}
else
{
lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; 
lean_dec(x_2085);
lean_dec(x_1566);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_2221 = lean_ctor_get(x_2212, 0);
lean_inc(x_2221);
x_2222 = lean_ctor_get(x_2212, 1);
lean_inc(x_2222);
if (lean_is_exclusive(x_2212)) {
 lean_ctor_release(x_2212, 0);
 lean_ctor_release(x_2212, 1);
 x_2223 = x_2212;
} else {
 lean_dec_ref(x_2212);
 x_2223 = lean_box(0);
}
if (lean_is_scalar(x_2223)) {
 x_2224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2224 = x_2223;
}
lean_ctor_set(x_2224, 0, x_2221);
lean_ctor_set(x_2224, 1, x_2222);
return x_2224;
}
}
block_2141:
{
uint8_t x_2088; 
lean_dec(x_2087);
x_2088 = l_Array_isEmpty___rarg(x_11);
if (x_2088 == 0)
{
lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_2089 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2089, 0, x_1564);
x_2090 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2091 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2091, 0, x_2090);
lean_ctor_set(x_2091, 1, x_2089);
x_2092 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2093 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2093, 0, x_2091);
lean_ctor_set(x_2093, 1, x_2092);
x_2094 = x_11;
x_2095 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1568, x_2094);
x_2096 = x_2095;
x_2097 = l_Array_toList___rarg(x_2096);
lean_dec(x_2096);
x_2098 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2097);
x_2099 = l_Array_HasRepr___rarg___closed__1;
x_2100 = lean_string_append(x_2099, x_2098);
lean_dec(x_2098);
x_2101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2101, 0, x_2100);
x_2102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2102, 0, x_2101);
x_2103 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2103, 0, x_2093);
lean_ctor_set(x_2103, 1, x_2102);
x_2104 = l_Lean_Elab_Term_throwError___rarg(x_2103, x_1487, x_2086);
return x_2104;
}
else
{
lean_object* x_2105; lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; uint8_t x_2137; 
lean_dec(x_1564);
lean_dec(x_11);
x_2130 = l_Lean_Elab_Term_getOptions(x_1487, x_2086);
x_2131 = lean_ctor_get(x_2130, 0);
lean_inc(x_2131);
x_2132 = lean_ctor_get(x_2130, 1);
lean_inc(x_2132);
lean_dec(x_2130);
x_2133 = l_Lean_Elab_Term_getCurrRef(x_1487, x_2132);
x_2134 = lean_ctor_get(x_2133, 0);
lean_inc(x_2134);
x_2135 = lean_ctor_get(x_2133, 1);
lean_inc(x_2135);
lean_dec(x_2133);
x_2136 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2137 = l_Lean_checkTraceOption(x_2131, x_2136);
lean_dec(x_2131);
if (x_2137 == 0)
{
lean_dec(x_2134);
x_2105 = x_2135;
goto block_2129;
}
else
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; 
lean_inc(x_2);
x_2138 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2138, 0, x_2);
lean_inc(x_1487);
x_2139 = l_Lean_Elab_Term_logTrace(x_2136, x_2134, x_2138, x_1487, x_2135);
lean_dec(x_2134);
x_2140 = lean_ctor_get(x_2139, 1);
lean_inc(x_2140);
lean_dec(x_2139);
x_2105 = x_2140;
goto block_2129;
}
block_2129:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_2106; 
lean_dec(x_3);
x_2106 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_2105);
lean_dec(x_12);
if (lean_obj_tag(x_2106) == 0)
{
lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; 
x_2107 = lean_ctor_get(x_2106, 1);
lean_inc(x_2107);
if (lean_is_exclusive(x_2106)) {
 lean_ctor_release(x_2106, 0);
 lean_ctor_release(x_2106, 1);
 x_2108 = x_2106;
} else {
 lean_dec_ref(x_2106);
 x_2108 = lean_box(0);
}
if (lean_is_scalar(x_2108)) {
 x_2109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2109 = x_2108;
}
lean_ctor_set(x_2109, 0, x_2);
lean_ctor_set(x_2109, 1, x_2107);
return x_2109;
}
else
{
lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; 
lean_dec(x_2);
x_2110 = lean_ctor_get(x_2106, 0);
lean_inc(x_2110);
x_2111 = lean_ctor_get(x_2106, 1);
lean_inc(x_2111);
if (lean_is_exclusive(x_2106)) {
 lean_ctor_release(x_2106, 0);
 lean_ctor_release(x_2106, 1);
 x_2112 = x_2106;
} else {
 lean_dec_ref(x_2106);
 x_2112 = lean_box(0);
}
if (lean_is_scalar(x_2112)) {
 x_2113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2113 = x_2112;
}
lean_ctor_set(x_2113, 0, x_2110);
lean_ctor_set(x_2113, 1, x_2111);
return x_2113;
}
}
else
{
lean_object* x_2114; lean_object* x_2115; 
x_2114 = lean_ctor_get(x_8, 0);
lean_inc(x_2114);
lean_dec(x_8);
lean_inc(x_1487);
x_2115 = l_Lean_Elab_Term_isDefEq(x_2114, x_3, x_1487, x_2105);
if (lean_obj_tag(x_2115) == 0)
{
lean_object* x_2116; lean_object* x_2117; 
x_2116 = lean_ctor_get(x_2115, 1);
lean_inc(x_2116);
lean_dec(x_2115);
x_2117 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1568, x_1487, x_2116);
lean_dec(x_12);
if (lean_obj_tag(x_2117) == 0)
{
lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; 
x_2118 = lean_ctor_get(x_2117, 1);
lean_inc(x_2118);
if (lean_is_exclusive(x_2117)) {
 lean_ctor_release(x_2117, 0);
 lean_ctor_release(x_2117, 1);
 x_2119 = x_2117;
} else {
 lean_dec_ref(x_2117);
 x_2119 = lean_box(0);
}
if (lean_is_scalar(x_2119)) {
 x_2120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2120 = x_2119;
}
lean_ctor_set(x_2120, 0, x_2);
lean_ctor_set(x_2120, 1, x_2118);
return x_2120;
}
else
{
lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; 
lean_dec(x_2);
x_2121 = lean_ctor_get(x_2117, 0);
lean_inc(x_2121);
x_2122 = lean_ctor_get(x_2117, 1);
lean_inc(x_2122);
if (lean_is_exclusive(x_2117)) {
 lean_ctor_release(x_2117, 0);
 lean_ctor_release(x_2117, 1);
 x_2123 = x_2117;
} else {
 lean_dec_ref(x_2117);
 x_2123 = lean_box(0);
}
if (lean_is_scalar(x_2123)) {
 x_2124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2124 = x_2123;
}
lean_ctor_set(x_2124, 0, x_2121);
lean_ctor_set(x_2124, 1, x_2122);
return x_2124;
}
}
else
{
lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; 
lean_dec(x_1487);
lean_dec(x_12);
lean_dec(x_2);
x_2125 = lean_ctor_get(x_2115, 0);
lean_inc(x_2125);
x_2126 = lean_ctor_get(x_2115, 1);
lean_inc(x_2126);
if (lean_is_exclusive(x_2115)) {
 lean_ctor_release(x_2115, 0);
 lean_ctor_release(x_2115, 1);
 x_2127 = x_2115;
} else {
 lean_dec_ref(x_2115);
 x_2127 = lean_box(0);
}
if (lean_is_scalar(x_2127)) {
 x_2128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2128 = x_2127;
}
lean_ctor_set(x_2128, 0, x_2125);
lean_ctor_set(x_2128, 1, x_2126);
return x_2128;
}
}
}
}
}
}
else
{
lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; 
lean_dec(x_2085);
lean_dec(x_2081);
lean_dec(x_1566);
lean_dec(x_1565);
lean_dec(x_1564);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_2225 = lean_ctor_get(x_2084, 0);
lean_inc(x_2225);
x_2226 = lean_ctor_get(x_2084, 1);
lean_inc(x_2226);
if (lean_is_exclusive(x_2084)) {
 lean_ctor_release(x_2084, 0);
 lean_ctor_release(x_2084, 1);
 x_2227 = x_2084;
} else {
 lean_dec_ref(x_2084);
 x_2227 = lean_box(0);
}
if (lean_is_scalar(x_2227)) {
 x_2228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2228 = x_2227;
}
lean_ctor_set(x_2228, 0, x_2225);
lean_ctor_set(x_2228, 1, x_2226);
return x_2228;
}
}
}
}
else
{
lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; 
lean_dec(x_1564);
lean_dec(x_3);
x_2229 = lean_ctor_get(x_1569, 0);
lean_inc(x_2229);
lean_dec(x_1569);
x_2230 = l_Lean_Elab_Term_NamedArg_inhabited;
x_2231 = lean_array_get(x_2230, x_11, x_2229);
x_2232 = l_Array_eraseIdx___rarg(x_11, x_2229);
lean_dec(x_2229);
x_2233 = lean_ctor_get(x_2231, 1);
lean_inc(x_2233);
lean_dec(x_2231);
lean_inc(x_1487);
lean_inc(x_2);
x_2234 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2233, x_1565, x_1487, x_1490);
if (lean_obj_tag(x_2234) == 0)
{
lean_object* x_2235; lean_object* x_2236; uint8_t x_2237; lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; 
x_2235 = lean_ctor_get(x_2234, 0);
lean_inc(x_2235);
x_2236 = lean_ctor_get(x_2234, 1);
lean_inc(x_2236);
lean_dec(x_2234);
x_2237 = 1;
x_2238 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_2238, 0, x_6);
lean_ctor_set(x_2238, 1, x_7);
lean_ctor_set(x_2238, 2, x_8);
lean_ctor_set(x_2238, 3, x_10);
lean_ctor_set(x_2238, 4, x_2232);
lean_ctor_set(x_2238, 5, x_12);
lean_ctor_set(x_2238, 6, x_13);
lean_ctor_set_uint8(x_2238, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2238, sizeof(void*)*7 + 1, x_2237);
lean_inc(x_2235);
x_2239 = l_Lean_mkApp(x_2, x_2235);
x_2240 = lean_expr_instantiate1(x_1566, x_2235);
lean_dec(x_2235);
lean_dec(x_1566);
lean_inc(x_1487);
x_2241 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1489, x_1487, x_2236);
if (lean_obj_tag(x_2241) == 0)
{
lean_object* x_2242; 
x_2242 = lean_ctor_get(x_2241, 1);
lean_inc(x_2242);
lean_dec(x_2241);
x_1 = x_2238;
x_2 = x_2239;
x_3 = x_2240;
x_4 = x_1487;
x_5 = x_2242;
goto _start;
}
else
{
lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; 
lean_dec(x_2240);
lean_dec(x_2239);
lean_dec(x_2238);
lean_dec(x_1487);
x_2244 = lean_ctor_get(x_2241, 0);
lean_inc(x_2244);
x_2245 = lean_ctor_get(x_2241, 1);
lean_inc(x_2245);
if (lean_is_exclusive(x_2241)) {
 lean_ctor_release(x_2241, 0);
 lean_ctor_release(x_2241, 1);
 x_2246 = x_2241;
} else {
 lean_dec_ref(x_2241);
 x_2246 = lean_box(0);
}
if (lean_is_scalar(x_2246)) {
 x_2247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2247 = x_2246;
}
lean_ctor_set(x_2247, 0, x_2244);
lean_ctor_set(x_2247, 1, x_2245);
return x_2247;
}
}
else
{
lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; 
lean_dec(x_2232);
lean_dec(x_1566);
lean_dec(x_1489);
lean_dec(x_1487);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_2248 = lean_ctor_get(x_2234, 0);
lean_inc(x_2248);
x_2249 = lean_ctor_get(x_2234, 1);
lean_inc(x_2249);
if (lean_is_exclusive(x_2234)) {
 lean_ctor_release(x_2234, 0);
 lean_ctor_release(x_2234, 1);
 x_2250 = x_2234;
} else {
 lean_dec_ref(x_2234);
 x_2250 = lean_box(0);
}
if (lean_is_scalar(x_2250)) {
 x_2251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2251 = x_2250;
}
lean_ctor_set(x_2251, 0, x_2248);
lean_ctor_set(x_2251, 1, x_2249);
return x_2251;
}
}
}
else
{
lean_object* x_2252; 
lean_dec(x_13);
lean_dec(x_6);
x_2252 = lean_box(0);
x_1491 = x_2252;
goto block_1563;
}
block_1563:
{
uint8_t x_1492; 
lean_dec(x_1491);
x_1492 = l_Array_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_1492 == 0)
{
lean_object* x_1493; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_inc(x_1487);
x_1493 = l___private_Lean_Elab_App_4__tryCoeFun(x_1489, x_2, x_1487, x_1490);
if (lean_obj_tag(x_1493) == 0)
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; 
x_1494 = lean_ctor_get(x_1493, 0);
lean_inc(x_1494);
x_1495 = lean_ctor_get(x_1493, 1);
lean_inc(x_1495);
lean_dec(x_1493);
lean_inc(x_1487);
lean_inc(x_1494);
x_1496 = l_Lean_Elab_Term_inferType(x_1494, x_1487, x_1495);
if (lean_obj_tag(x_1496) == 0)
{
lean_object* x_1497; lean_object* x_1498; 
x_1497 = lean_ctor_get(x_1496, 0);
lean_inc(x_1497);
x_1498 = lean_ctor_get(x_1496, 1);
lean_inc(x_1498);
lean_dec(x_1496);
x_2 = x_1494;
x_3 = x_1497;
x_4 = x_1487;
x_5 = x_1498;
goto _start;
}
else
{
lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; 
lean_dec(x_1494);
lean_dec(x_1487);
lean_dec(x_1);
x_1500 = lean_ctor_get(x_1496, 0);
lean_inc(x_1500);
x_1501 = lean_ctor_get(x_1496, 1);
lean_inc(x_1501);
if (lean_is_exclusive(x_1496)) {
 lean_ctor_release(x_1496, 0);
 lean_ctor_release(x_1496, 1);
 x_1502 = x_1496;
} else {
 lean_dec_ref(x_1496);
 x_1502 = lean_box(0);
}
if (lean_is_scalar(x_1502)) {
 x_1503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1503 = x_1502;
}
lean_ctor_set(x_1503, 0, x_1500);
lean_ctor_set(x_1503, 1, x_1501);
return x_1503;
}
}
else
{
lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; 
lean_dec(x_1487);
lean_dec(x_1);
x_1504 = lean_ctor_get(x_1493, 0);
lean_inc(x_1504);
x_1505 = lean_ctor_get(x_1493, 1);
lean_inc(x_1505);
if (lean_is_exclusive(x_1493)) {
 lean_ctor_release(x_1493, 0);
 lean_ctor_release(x_1493, 1);
 x_1506 = x_1493;
} else {
 lean_dec_ref(x_1493);
 x_1506 = lean_box(0);
}
if (lean_is_scalar(x_1506)) {
 x_1507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1507 = x_1506;
}
lean_ctor_set(x_1507, 0, x_1504);
lean_ctor_set(x_1507, 1, x_1505);
return x_1507;
}
}
else
{
lean_object* x_1508; uint8_t x_1509; 
x_1508 = lean_array_get_size(x_7);
lean_dec(x_7);
x_1509 = lean_nat_dec_eq(x_10, x_1508);
lean_dec(x_1508);
lean_dec(x_10);
if (x_1509 == 0)
{
lean_object* x_1510; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_inc(x_1487);
x_1510 = l___private_Lean_Elab_App_4__tryCoeFun(x_1489, x_2, x_1487, x_1490);
if (lean_obj_tag(x_1510) == 0)
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
x_1511 = lean_ctor_get(x_1510, 0);
lean_inc(x_1511);
x_1512 = lean_ctor_get(x_1510, 1);
lean_inc(x_1512);
lean_dec(x_1510);
lean_inc(x_1487);
lean_inc(x_1511);
x_1513 = l_Lean_Elab_Term_inferType(x_1511, x_1487, x_1512);
if (lean_obj_tag(x_1513) == 0)
{
lean_object* x_1514; lean_object* x_1515; 
x_1514 = lean_ctor_get(x_1513, 0);
lean_inc(x_1514);
x_1515 = lean_ctor_get(x_1513, 1);
lean_inc(x_1515);
lean_dec(x_1513);
x_2 = x_1511;
x_3 = x_1514;
x_4 = x_1487;
x_5 = x_1515;
goto _start;
}
else
{
lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; 
lean_dec(x_1511);
lean_dec(x_1487);
lean_dec(x_1);
x_1517 = lean_ctor_get(x_1513, 0);
lean_inc(x_1517);
x_1518 = lean_ctor_get(x_1513, 1);
lean_inc(x_1518);
if (lean_is_exclusive(x_1513)) {
 lean_ctor_release(x_1513, 0);
 lean_ctor_release(x_1513, 1);
 x_1519 = x_1513;
} else {
 lean_dec_ref(x_1513);
 x_1519 = lean_box(0);
}
if (lean_is_scalar(x_1519)) {
 x_1520 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1520 = x_1519;
}
lean_ctor_set(x_1520, 0, x_1517);
lean_ctor_set(x_1520, 1, x_1518);
return x_1520;
}
}
else
{
lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; 
lean_dec(x_1487);
lean_dec(x_1);
x_1521 = lean_ctor_get(x_1510, 0);
lean_inc(x_1521);
x_1522 = lean_ctor_get(x_1510, 1);
lean_inc(x_1522);
if (lean_is_exclusive(x_1510)) {
 lean_ctor_release(x_1510, 0);
 lean_ctor_release(x_1510, 1);
 x_1523 = x_1510;
} else {
 lean_dec_ref(x_1510);
 x_1523 = lean_box(0);
}
if (lean_is_scalar(x_1523)) {
 x_1524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1524 = x_1523;
}
lean_ctor_set(x_1524, 0, x_1521);
lean_ctor_set(x_1524, 1, x_1522);
return x_1524;
}
}
else
{
lean_object* x_1525; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; uint8_t x_1559; 
lean_dec(x_1489);
lean_dec(x_1);
x_1552 = l_Lean_Elab_Term_getOptions(x_1487, x_1490);
x_1553 = lean_ctor_get(x_1552, 0);
lean_inc(x_1553);
x_1554 = lean_ctor_get(x_1552, 1);
lean_inc(x_1554);
lean_dec(x_1552);
x_1555 = l_Lean_Elab_Term_getCurrRef(x_1487, x_1554);
x_1556 = lean_ctor_get(x_1555, 0);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1555, 1);
lean_inc(x_1557);
lean_dec(x_1555);
x_1558 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1559 = l_Lean_checkTraceOption(x_1553, x_1558);
lean_dec(x_1553);
if (x_1559 == 0)
{
lean_dec(x_1556);
x_1525 = x_1557;
goto block_1551;
}
else
{
lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; 
lean_inc(x_2);
x_1560 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1560, 0, x_2);
lean_inc(x_1487);
x_1561 = l_Lean_Elab_Term_logTrace(x_1558, x_1556, x_1560, x_1487, x_1557);
lean_dec(x_1556);
x_1562 = lean_ctor_get(x_1561, 1);
lean_inc(x_1562);
lean_dec(x_1561);
x_1525 = x_1562;
goto block_1551;
}
block_1551:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1526; lean_object* x_1527; 
lean_dec(x_3);
x_1526 = lean_unsigned_to_nat(0u);
x_1527 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1526, x_1487, x_1525);
lean_dec(x_12);
if (lean_obj_tag(x_1527) == 0)
{
lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; 
x_1528 = lean_ctor_get(x_1527, 1);
lean_inc(x_1528);
if (lean_is_exclusive(x_1527)) {
 lean_ctor_release(x_1527, 0);
 lean_ctor_release(x_1527, 1);
 x_1529 = x_1527;
} else {
 lean_dec_ref(x_1527);
 x_1529 = lean_box(0);
}
if (lean_is_scalar(x_1529)) {
 x_1530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1530 = x_1529;
}
lean_ctor_set(x_1530, 0, x_2);
lean_ctor_set(x_1530, 1, x_1528);
return x_1530;
}
else
{
lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; 
lean_dec(x_2);
x_1531 = lean_ctor_get(x_1527, 0);
lean_inc(x_1531);
x_1532 = lean_ctor_get(x_1527, 1);
lean_inc(x_1532);
if (lean_is_exclusive(x_1527)) {
 lean_ctor_release(x_1527, 0);
 lean_ctor_release(x_1527, 1);
 x_1533 = x_1527;
} else {
 lean_dec_ref(x_1527);
 x_1533 = lean_box(0);
}
if (lean_is_scalar(x_1533)) {
 x_1534 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1534 = x_1533;
}
lean_ctor_set(x_1534, 0, x_1531);
lean_ctor_set(x_1534, 1, x_1532);
return x_1534;
}
}
else
{
lean_object* x_1535; lean_object* x_1536; 
x_1535 = lean_ctor_get(x_8, 0);
lean_inc(x_1535);
lean_dec(x_8);
lean_inc(x_1487);
x_1536 = l_Lean_Elab_Term_isDefEq(x_1535, x_3, x_1487, x_1525);
if (lean_obj_tag(x_1536) == 0)
{
lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; 
x_1537 = lean_ctor_get(x_1536, 1);
lean_inc(x_1537);
lean_dec(x_1536);
x_1538 = lean_unsigned_to_nat(0u);
x_1539 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1538, x_1487, x_1537);
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
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
lean_dec(x_1487);
lean_dec(x_12);
lean_dec(x_2);
x_1547 = lean_ctor_get(x_1536, 0);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1536, 1);
lean_inc(x_1548);
if (lean_is_exclusive(x_1536)) {
 lean_ctor_release(x_1536, 0);
 lean_ctor_release(x_1536, 1);
 x_1549 = x_1536;
} else {
 lean_dec_ref(x_1536);
 x_1549 = lean_box(0);
}
if (lean_is_scalar(x_1549)) {
 x_1550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1550 = x_1549;
}
lean_ctor_set(x_1550, 0, x_1547);
lean_ctor_set(x_1550, 1, x_1548);
return x_1550;
}
}
}
}
}
}
}
else
{
lean_object* x_2253; lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; 
lean_dec(x_1487);
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
x_2253 = lean_ctor_get(x_1488, 0);
lean_inc(x_2253);
x_2254 = lean_ctor_get(x_1488, 1);
lean_inc(x_2254);
if (lean_is_exclusive(x_1488)) {
 lean_ctor_release(x_1488, 0);
 lean_ctor_release(x_1488, 1);
 x_2255 = x_1488;
} else {
 lean_dec_ref(x_1488);
 x_2255 = lean_box(0);
}
if (lean_is_scalar(x_2255)) {
 x_2256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2256 = x_2255;
}
lean_ctor_set(x_2256, 0, x_2253);
lean_ctor_set(x_2256, 1, x_2254);
return x_2256;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; 
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
x_14 = l_Array_isEmpty___rarg(x_2);
x_15 = l_Lean_Elab_Term_getOptions(x_6, x_13);
if (x_14 == 0)
{
uint8_t x_69; 
x_69 = 0;
x_16 = x_69;
goto block_68;
}
else
{
uint8_t x_70; 
x_70 = l_Array_isEmpty___rarg(x_3);
x_16 = x_70;
goto block_68;
}
block_68:
{
uint8_t x_17; 
if (x_16 == 0)
{
uint8_t x_66; 
x_66 = 0;
x_17 = x_66;
goto block_65;
}
else
{
uint8_t x_67; 
x_67 = 1;
x_17 = x_67;
goto block_65;
}
block_65:
{
lean_object* x_18; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_dec(x_15);
x_44 = l_Lean_Elab_Term_getCurrRef(x_6, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l___private_Lean_Elab_App_11__elabAppArgs___closed__2;
x_48 = l_Lean_checkTraceOption(x_42, x_47);
lean_dec(x_42);
if (x_48 == 0)
{
lean_dec(x_45);
x_18 = x_46;
goto block_41;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_inc(x_1);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_1);
lean_inc(x_12);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_12);
if (x_5 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l___private_Lean_Elab_App_11__elabAppArgs___closed__8;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
x_53 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
lean_inc(x_6);
x_56 = l_Lean_Elab_Term_logTrace(x_47, x_45, x_55, x_6, x_46);
lean_dec(x_45);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_18 = x_57;
goto block_41;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = l___private_Lean_Elab_App_11__elabAppArgs___closed__11;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_49);
x_60 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_50);
lean_inc(x_6);
x_63 = l_Lean_Elab_Term_logTrace(x_47, x_45, x_62, x_6, x_46);
lean_dec(x_45);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_18 = x_64;
goto block_41;
}
}
block_41:
{
if (x_17 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Elab_Term_tryPostponeIfMVar(x_12, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_Term_getCurrRef(x_6, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_empty___closed__1;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_2);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*7, x_5);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 1, x_26);
x_28 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_27, x_1, x_12, x_6, x_23);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = l_Lean_Elab_Term_getCurrRef(x_6, x_18);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Array_empty___closed__1;
x_38 = 0;
x_39 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_3);
lean_ctor_set(x_39, 2, x_4);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_2);
lean_ctor_set(x_39, 5, x_37);
lean_ctor_set(x_39, 6, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*7, x_5);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 1, x_38);
x_40 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_39, x_1, x_12, x_6, x_35);
return x_40;
}
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_8);
if (x_71 == 0)
{
return x_8;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_8, 0);
x_73 = lean_ctor_get(x_8, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_8);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
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
uint8_t x_83; 
x_83 = 0;
x_17 = x_83;
goto block_82;
}
else
{
uint8_t x_84; 
x_84 = 1;
x_17 = x_84;
goto block_82;
}
block_82:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_5;
goto block_75;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_76 = l___private_Lean_Elab_App_13__resolveLValAux___closed__18;
x_77 = l_Lean_Elab_Term_throwError___rarg(x_76, x_4, x_5);
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
block_75:
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Elab_Term_getEnv___rarg(x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_13);
lean_inc(x_21);
x_23 = l_Lean_isStructureLike(x_21, x_13);
lean_inc(x_13);
lean_inc(x_21);
x_24 = l_Lean_getStructureFields(x_21, x_13);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_14, x_25);
lean_dec(x_14);
x_27 = lean_array_get_size(x_24);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_23 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_free_object(x_19);
lean_dec(x_21);
lean_dec(x_13);
x_29 = l___private_Lean_Elab_App_13__resolveLValAux___closed__9;
x_30 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_29, x_4, x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
if (x_28 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_24);
lean_free_object(x_19);
lean_dec(x_21);
lean_dec(x_13);
x_35 = l_Nat_repr(x_27);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l___private_Lean_Elab_App_13__resolveLValAux___closed__12;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Elab_App_13__resolveLValAux___closed__15;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_41, x_4, x_22);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_13);
x_43 = l_Lean_isStructure(x_21, x_13);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_24);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_26);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_array_fget(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
lean_inc(x_13);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_13);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_19, 0, x_46);
return x_19;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_47 = lean_ctor_get(x_19, 0);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_19);
lean_inc(x_13);
lean_inc(x_47);
x_49 = l_Lean_isStructureLike(x_47, x_13);
lean_inc(x_13);
lean_inc(x_47);
x_50 = l_Lean_getStructureFields(x_47, x_13);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_14, x_51);
lean_dec(x_14);
x_53 = lean_array_get_size(x_50);
x_54 = lean_nat_dec_lt(x_52, x_53);
if (x_49 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_13);
x_55 = l___private_Lean_Elab_App_13__resolveLValAux___closed__9;
x_56 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_55, x_4, x_48);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
if (x_54 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_13);
x_61 = l_Nat_repr(x_53);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l___private_Lean_Elab_App_13__resolveLValAux___closed__12;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l___private_Lean_Elab_App_13__resolveLValAux___closed__15;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_67, x_4, x_48);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_13);
x_69 = l_Lean_isStructure(x_47, x_13);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_50);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_13);
lean_ctor_set(x_70, 1, x_52);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_48);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_array_fget(x_50, x_52);
lean_dec(x_52);
lean_dec(x_50);
lean_inc(x_13);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_13);
lean_ctor_set(x_73, 1, x_13);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_48);
return x_74;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_12, 0);
lean_inc(x_85);
lean_dec(x_12);
x_86 = lean_ctor_get(x_3, 0);
lean_inc(x_86);
lean_dec(x_3);
x_87 = l_Lean_Elab_Term_getEnv___rarg(x_5);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_85);
lean_inc(x_89);
x_91 = l_Lean_isStructure(x_89, x_85);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_free_object(x_87);
x_92 = lean_box(0);
lean_inc(x_86);
x_93 = lean_name_mk_string(x_92, x_86);
x_94 = l_Lean_Name_append___main(x_85, x_93);
x_95 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_90);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_94);
x_98 = l_Lean_Name_replacePrefix___main(x_94, x_96, x_92);
lean_dec(x_96);
x_99 = l_Lean_Elab_Term_getLCtx(x_4, x_97);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = lean_local_ctx_find_from_user_name(x_101, x_98);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
lean_inc(x_94);
lean_inc(x_89);
x_104 = lean_environment_find(x_89, x_94);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_inc(x_94);
lean_inc(x_89);
x_105 = l_Lean_mkPrivateName(x_89, x_94);
lean_inc(x_105);
x_106 = lean_environment_find(x_89, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_105);
lean_free_object(x_99);
lean_dec(x_85);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_86);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_110 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_112 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_113, 0, x_94);
x_114 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_116 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_116, x_4, x_102);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_106);
lean_dec(x_94);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_85);
lean_ctor_set(x_118, 1, x_105);
lean_ctor_set(x_99, 0, x_118);
return x_99;
}
}
else
{
lean_object* x_119; 
lean_dec(x_104);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_85);
lean_ctor_set(x_119, 1, x_94);
lean_ctor_set(x_99, 0, x_119);
return x_99;
}
}
else
{
lean_object* x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_103, 0);
lean_inc(x_120);
lean_dec(x_103);
x_121 = l_Lean_LocalDecl_binderInfo(x_120);
x_122 = 4;
x_123 = l_Lean_BinderInfo_beq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_120);
lean_inc(x_94);
lean_inc(x_89);
x_124 = lean_environment_find(x_89, x_94);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_inc(x_94);
lean_inc(x_89);
x_125 = l_Lean_mkPrivateName(x_89, x_94);
lean_inc(x_125);
x_126 = lean_environment_find(x_89, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_125);
lean_free_object(x_99);
lean_dec(x_85);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_86);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_130 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_133, 0, x_94);
x_134 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_136, x_4, x_102);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_126);
lean_dec(x_94);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_85);
lean_ctor_set(x_138, 1, x_125);
lean_ctor_set(x_99, 0, x_138);
return x_99;
}
}
else
{
lean_object* x_139; 
lean_dec(x_124);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_85);
lean_ctor_set(x_139, 1, x_94);
lean_ctor_set(x_99, 0, x_139);
return x_99;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_140 = l_Lean_LocalDecl_toExpr(x_120);
lean_dec(x_120);
x_141 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_141, 0, x_85);
lean_ctor_set(x_141, 1, x_94);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_99, 0, x_141);
return x_99;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_99, 0);
x_143 = lean_ctor_get(x_99, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_99);
x_144 = lean_local_ctx_find_from_user_name(x_142, x_98);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_inc(x_94);
lean_inc(x_89);
x_145 = lean_environment_find(x_89, x_94);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_inc(x_94);
lean_inc(x_89);
x_146 = l_Lean_mkPrivateName(x_89, x_94);
lean_inc(x_146);
x_147 = lean_environment_find(x_89, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_146);
lean_dec(x_85);
x_148 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_148, 0, x_86);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_151 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_153 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_154, 0, x_94);
x_155 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_157 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_157, x_4, x_143);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_147);
lean_dec(x_94);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_85);
lean_ctor_set(x_159, 1, x_146);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_143);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_145);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_85);
lean_ctor_set(x_161, 1, x_94);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_143);
return x_162;
}
}
else
{
lean_object* x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_144, 0);
lean_inc(x_163);
lean_dec(x_144);
x_164 = l_Lean_LocalDecl_binderInfo(x_163);
x_165 = 4;
x_166 = l_Lean_BinderInfo_beq(x_164, x_165);
if (x_166 == 0)
{
lean_object* x_167; 
lean_dec(x_163);
lean_inc(x_94);
lean_inc(x_89);
x_167 = lean_environment_find(x_89, x_94);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_inc(x_94);
lean_inc(x_89);
x_168 = l_Lean_mkPrivateName(x_89, x_94);
lean_inc(x_168);
x_169 = lean_environment_find(x_89, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_168);
lean_dec(x_85);
x_170 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_170, 0, x_86);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_173 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_175 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_176, 0, x_94);
x_177 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_179 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_179, x_4, x_143);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_169);
lean_dec(x_94);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_85);
lean_ctor_set(x_181, 1, x_168);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_143);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_167);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_85);
lean_ctor_set(x_183, 1, x_94);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_143);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_185 = l_Lean_LocalDecl_toExpr(x_163);
lean_dec(x_163);
x_186 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_186, 0, x_85);
lean_ctor_set(x_186, 1, x_94);
lean_ctor_set(x_186, 2, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_143);
return x_187;
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_box(0);
lean_inc(x_86);
x_189 = lean_name_mk_string(x_188, x_86);
lean_inc(x_85);
lean_inc(x_89);
x_190 = l_Lean_findField_x3f___main(x_89, x_85, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_free_object(x_87);
x_191 = l_Lean_Name_append___main(x_85, x_189);
x_192 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_90);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_191);
x_195 = l_Lean_Name_replacePrefix___main(x_191, x_193, x_188);
lean_dec(x_193);
x_196 = l_Lean_Elab_Term_getLCtx(x_4, x_194);
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_196, 0);
x_199 = lean_ctor_get(x_196, 1);
x_200 = lean_local_ctx_find_from_user_name(x_198, x_195);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
lean_inc(x_191);
lean_inc(x_89);
x_201 = lean_environment_find(x_89, x_191);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_inc(x_191);
lean_inc(x_89);
x_202 = l_Lean_mkPrivateName(x_89, x_191);
lean_inc(x_202);
x_203 = lean_environment_find(x_89, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_202);
lean_free_object(x_196);
lean_dec(x_85);
x_204 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_204, 0, x_86);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_207 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_209 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_210, 0, x_191);
x_211 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_213 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_214 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_213, x_4, x_199);
return x_214;
}
else
{
lean_object* x_215; 
lean_dec(x_203);
lean_dec(x_191);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_85);
lean_ctor_set(x_215, 1, x_202);
lean_ctor_set(x_196, 0, x_215);
return x_196;
}
}
else
{
lean_object* x_216; 
lean_dec(x_201);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_216 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_216, 0, x_85);
lean_ctor_set(x_216, 1, x_191);
lean_ctor_set(x_196, 0, x_216);
return x_196;
}
}
else
{
lean_object* x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; 
x_217 = lean_ctor_get(x_200, 0);
lean_inc(x_217);
lean_dec(x_200);
x_218 = l_Lean_LocalDecl_binderInfo(x_217);
x_219 = 4;
x_220 = l_Lean_BinderInfo_beq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_217);
lean_inc(x_191);
lean_inc(x_89);
x_221 = lean_environment_find(x_89, x_191);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_inc(x_191);
lean_inc(x_89);
x_222 = l_Lean_mkPrivateName(x_89, x_191);
lean_inc(x_222);
x_223 = lean_environment_find(x_89, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_222);
lean_free_object(x_196);
lean_dec(x_85);
x_224 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_224, 0, x_86);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_227 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_229 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_230, 0, x_191);
x_231 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_233 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_233, x_4, x_199);
return x_234;
}
else
{
lean_object* x_235; 
lean_dec(x_223);
lean_dec(x_191);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_235 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_235, 0, x_85);
lean_ctor_set(x_235, 1, x_222);
lean_ctor_set(x_196, 0, x_235);
return x_196;
}
}
else
{
lean_object* x_236; 
lean_dec(x_221);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_85);
lean_ctor_set(x_236, 1, x_191);
lean_ctor_set(x_196, 0, x_236);
return x_196;
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_237 = l_Lean_LocalDecl_toExpr(x_217);
lean_dec(x_217);
x_238 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_238, 0, x_85);
lean_ctor_set(x_238, 1, x_191);
lean_ctor_set(x_238, 2, x_237);
lean_ctor_set(x_196, 0, x_238);
return x_196;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_196, 0);
x_240 = lean_ctor_get(x_196, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_196);
x_241 = lean_local_ctx_find_from_user_name(x_239, x_195);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; 
lean_inc(x_191);
lean_inc(x_89);
x_242 = lean_environment_find(x_89, x_191);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; 
lean_inc(x_191);
lean_inc(x_89);
x_243 = l_Lean_mkPrivateName(x_89, x_191);
lean_inc(x_243);
x_244 = lean_environment_find(x_89, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_243);
lean_dec(x_85);
x_245 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_245, 0, x_86);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_247 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_248 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_250 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_251, 0, x_191);
x_252 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_254 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_254, x_4, x_240);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_244);
lean_dec(x_191);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_256 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_256, 0, x_85);
lean_ctor_set(x_256, 1, x_243);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_240);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_242);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_85);
lean_ctor_set(x_258, 1, x_191);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_240);
return x_259;
}
}
else
{
lean_object* x_260; uint8_t x_261; uint8_t x_262; uint8_t x_263; 
x_260 = lean_ctor_get(x_241, 0);
lean_inc(x_260);
lean_dec(x_241);
x_261 = l_Lean_LocalDecl_binderInfo(x_260);
x_262 = 4;
x_263 = l_Lean_BinderInfo_beq(x_261, x_262);
if (x_263 == 0)
{
lean_object* x_264; 
lean_dec(x_260);
lean_inc(x_191);
lean_inc(x_89);
x_264 = lean_environment_find(x_89, x_191);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; 
lean_inc(x_191);
lean_inc(x_89);
x_265 = l_Lean_mkPrivateName(x_89, x_191);
lean_inc(x_265);
x_266 = lean_environment_find(x_89, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_265);
lean_dec(x_85);
x_267 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_267, 0, x_86);
x_268 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_268, 0, x_267);
x_269 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_270 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
x_271 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_272 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_273, 0, x_191);
x_274 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
x_275 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_276 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_276, x_4, x_240);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_266);
lean_dec(x_191);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_278 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_278, 0, x_85);
lean_ctor_set(x_278, 1, x_265);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_240);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_264);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_280 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_280, 0, x_85);
lean_ctor_set(x_280, 1, x_191);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_240);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_282 = l_Lean_LocalDecl_toExpr(x_260);
lean_dec(x_260);
x_283 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_283, 0, x_85);
lean_ctor_set(x_283, 1, x_191);
lean_ctor_set(x_283, 2, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_240);
return x_284;
}
}
}
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_285 = lean_ctor_get(x_190, 0);
lean_inc(x_285);
lean_dec(x_190);
x_286 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_85);
lean_ctor_set(x_286, 2, x_189);
lean_ctor_set(x_87, 0, x_286);
return x_87;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_287 = lean_ctor_get(x_87, 0);
x_288 = lean_ctor_get(x_87, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_87);
lean_inc(x_85);
lean_inc(x_287);
x_289 = l_Lean_isStructure(x_287, x_85);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_290 = lean_box(0);
lean_inc(x_86);
x_291 = lean_name_mk_string(x_290, x_86);
x_292 = l_Lean_Name_append___main(x_85, x_291);
x_293 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_288);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
lean_inc(x_292);
x_296 = l_Lean_Name_replacePrefix___main(x_292, x_294, x_290);
lean_dec(x_294);
x_297 = l_Lean_Elab_Term_getLCtx(x_4, x_295);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
x_301 = lean_local_ctx_find_from_user_name(x_298, x_296);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; 
lean_inc(x_292);
lean_inc(x_287);
x_302 = lean_environment_find(x_287, x_292);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; 
lean_inc(x_292);
lean_inc(x_287);
x_303 = l_Lean_mkPrivateName(x_287, x_292);
lean_inc(x_303);
x_304 = lean_environment_find(x_287, x_303);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_303);
lean_dec(x_300);
lean_dec(x_85);
x_305 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_305, 0, x_86);
x_306 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_306, 0, x_305);
x_307 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_308 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_306);
x_309 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_310 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_311, 0, x_292);
x_312 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
x_313 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_314 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_314, x_4, x_299);
return x_315;
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_304);
lean_dec(x_292);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_316 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_316, 0, x_85);
lean_ctor_set(x_316, 1, x_303);
if (lean_is_scalar(x_300)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_300;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_299);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_302);
lean_dec(x_287);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_318 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_318, 0, x_85);
lean_ctor_set(x_318, 1, x_292);
if (lean_is_scalar(x_300)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_300;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_299);
return x_319;
}
}
else
{
lean_object* x_320; uint8_t x_321; uint8_t x_322; uint8_t x_323; 
x_320 = lean_ctor_get(x_301, 0);
lean_inc(x_320);
lean_dec(x_301);
x_321 = l_Lean_LocalDecl_binderInfo(x_320);
x_322 = 4;
x_323 = l_Lean_BinderInfo_beq(x_321, x_322);
if (x_323 == 0)
{
lean_object* x_324; 
lean_dec(x_320);
lean_inc(x_292);
lean_inc(x_287);
x_324 = lean_environment_find(x_287, x_292);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; 
lean_inc(x_292);
lean_inc(x_287);
x_325 = l_Lean_mkPrivateName(x_287, x_292);
lean_inc(x_325);
x_326 = lean_environment_find(x_287, x_325);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_325);
lean_dec(x_300);
lean_dec(x_85);
x_327 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_327, 0, x_86);
x_328 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_328, 0, x_327);
x_329 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_330 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_332 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_333, 0, x_292);
x_334 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_335 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_336 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
x_337 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_336, x_4, x_299);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_326);
lean_dec(x_292);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_338 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_338, 0, x_85);
lean_ctor_set(x_338, 1, x_325);
if (lean_is_scalar(x_300)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_300;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_299);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_324);
lean_dec(x_287);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_340 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_340, 0, x_85);
lean_ctor_set(x_340, 1, x_292);
if (lean_is_scalar(x_300)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_300;
}
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_299);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_287);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_342 = l_Lean_LocalDecl_toExpr(x_320);
lean_dec(x_320);
x_343 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_343, 0, x_85);
lean_ctor_set(x_343, 1, x_292);
lean_ctor_set(x_343, 2, x_342);
if (lean_is_scalar(x_300)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_300;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_299);
return x_344;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_box(0);
lean_inc(x_86);
x_346 = lean_name_mk_string(x_345, x_86);
lean_inc(x_85);
lean_inc(x_287);
x_347 = l_Lean_findField_x3f___main(x_287, x_85, x_346);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_348 = l_Lean_Name_append___main(x_85, x_346);
x_349 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_288);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
lean_inc(x_348);
x_352 = l_Lean_Name_replacePrefix___main(x_348, x_350, x_345);
lean_dec(x_350);
x_353 = l_Lean_Elab_Term_getLCtx(x_4, x_351);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_356 = x_353;
} else {
 lean_dec_ref(x_353);
 x_356 = lean_box(0);
}
x_357 = lean_local_ctx_find_from_user_name(x_354, x_352);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
lean_inc(x_348);
lean_inc(x_287);
x_358 = lean_environment_find(x_287, x_348);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; 
lean_inc(x_348);
lean_inc(x_287);
x_359 = l_Lean_mkPrivateName(x_287, x_348);
lean_inc(x_359);
x_360 = lean_environment_find(x_287, x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_359);
lean_dec(x_356);
lean_dec(x_85);
x_361 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_361, 0, x_86);
x_362 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_362, 0, x_361);
x_363 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_364 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_362);
x_365 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_366 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_367, 0, x_348);
x_368 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
x_369 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_370 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_371 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_370, x_4, x_355);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; 
lean_dec(x_360);
lean_dec(x_348);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_372 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_372, 0, x_85);
lean_ctor_set(x_372, 1, x_359);
if (lean_is_scalar(x_356)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_356;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_355);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_358);
lean_dec(x_287);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_374 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_374, 0, x_85);
lean_ctor_set(x_374, 1, x_348);
if (lean_is_scalar(x_356)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_356;
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_355);
return x_375;
}
}
else
{
lean_object* x_376; uint8_t x_377; uint8_t x_378; uint8_t x_379; 
x_376 = lean_ctor_get(x_357, 0);
lean_inc(x_376);
lean_dec(x_357);
x_377 = l_Lean_LocalDecl_binderInfo(x_376);
x_378 = 4;
x_379 = l_Lean_BinderInfo_beq(x_377, x_378);
if (x_379 == 0)
{
lean_object* x_380; 
lean_dec(x_376);
lean_inc(x_348);
lean_inc(x_287);
x_380 = lean_environment_find(x_287, x_348);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; 
lean_inc(x_348);
lean_inc(x_287);
x_381 = l_Lean_mkPrivateName(x_287, x_348);
lean_inc(x_381);
x_382 = lean_environment_find(x_287, x_381);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_381);
lean_dec(x_356);
lean_dec(x_85);
x_383 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_383, 0, x_86);
x_384 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_384, 0, x_383);
x_385 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_386 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_384);
x_387 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_388 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
x_389 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_389, 0, x_348);
x_390 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_392 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
x_393 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_392, x_4, x_355);
return x_393;
}
else
{
lean_object* x_394; lean_object* x_395; 
lean_dec(x_382);
lean_dec(x_348);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_394 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_394, 0, x_85);
lean_ctor_set(x_394, 1, x_381);
if (lean_is_scalar(x_356)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_356;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_355);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_380);
lean_dec(x_287);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_396 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_396, 0, x_85);
lean_ctor_set(x_396, 1, x_348);
if (lean_is_scalar(x_356)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_356;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_355);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_287);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_398 = l_Lean_LocalDecl_toExpr(x_376);
lean_dec(x_376);
x_399 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_399, 0, x_85);
lean_ctor_set(x_399, 1, x_348);
lean_ctor_set(x_399, 2, x_398);
if (lean_is_scalar(x_356)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_356;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_355);
return x_400;
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_287);
lean_dec(x_86);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_401 = lean_ctor_get(x_347, 0);
lean_inc(x_401);
lean_dec(x_347);
x_402 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_85);
lean_ctor_set(x_402, 2, x_346);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_288);
return x_403;
}
}
}
}
default: 
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_404 = lean_ctor_get(x_12, 0);
lean_inc(x_404);
lean_dec(x_12);
x_405 = lean_ctor_get(x_3, 0);
lean_inc(x_405);
lean_dec(x_3);
x_406 = l_Lean_Elab_Term_getEnv___rarg(x_5);
x_407 = !lean_is_exclusive(x_406);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_408 = lean_ctor_get(x_406, 0);
x_409 = lean_ctor_get(x_406, 1);
x_410 = l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
x_411 = lean_name_mk_string(x_404, x_410);
lean_inc(x_411);
x_412 = lean_environment_find(x_408, x_411);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_free_object(x_406);
lean_dec(x_405);
x_413 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_413, 0, x_411);
x_414 = l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
x_415 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_413);
x_416 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_417 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
x_418 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_417, x_4, x_409);
return x_418;
}
else
{
lean_object* x_419; 
lean_dec(x_412);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_419 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_419, 0, x_411);
lean_ctor_set(x_419, 1, x_405);
lean_ctor_set(x_406, 0, x_419);
return x_406;
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_420 = lean_ctor_get(x_406, 0);
x_421 = lean_ctor_get(x_406, 1);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_406);
x_422 = l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
x_423 = lean_name_mk_string(x_404, x_422);
lean_inc(x_423);
x_424 = lean_environment_find(x_420, x_423);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_405);
x_425 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_425, 0, x_423);
x_426 = l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
x_427 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_425);
x_428 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_429 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
x_430 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_429, x_4, x_421);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_424);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_431 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_431, 0, x_423);
lean_ctor_set(x_431, 1, x_405);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_421);
return x_432;
}
}
}
}
}
else
{
lean_object* x_433; 
lean_dec(x_12);
x_433 = lean_box(0);
x_6 = x_433;
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
x_14 = l_Std_PersistentArray_push___rarg(x_13, x_1);
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
x_22 = l_Std_PersistentArray_push___rarg(x_18, x_1);
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
x_38 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
x_16 = lean_ctor_get(x_9, 2);
x_17 = lean_ctor_get(x_9, 3);
x_18 = lean_ctor_get(x_9, 4);
x_19 = lean_ctor_get(x_9, 5);
x_20 = lean_ctor_get(x_9, 6);
x_21 = lean_ctor_get(x_9, 7);
x_22 = lean_ctor_get(x_9, 8);
x_23 = lean_ctor_get(x_9, 9);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*11);
x_25 = lean_ctor_get_uint8(x_9, sizeof(void*)*11 + 1);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*11 + 2);
x_27 = lean_ctor_get(x_9, 10);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_ctor_set(x_9, 10, x_1);
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
x_36 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_15);
lean_ctor_set(x_36, 2, x_16);
lean_ctor_set(x_36, 3, x_17);
lean_ctor_set(x_36, 4, x_18);
lean_ctor_set(x_36, 5, x_19);
lean_ctor_set(x_36, 6, x_20);
lean_ctor_set(x_36, 7, x_21);
lean_ctor_set(x_36, 8, x_22);
lean_ctor_set(x_36, 9, x_23);
lean_ctor_set(x_36, 10, x_27);
lean_ctor_set_uint8(x_36, sizeof(void*)*11, x_24);
lean_ctor_set_uint8(x_36, sizeof(void*)*11 + 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*11 + 2, x_26);
x_37 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_29, x_36, x_30);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_15);
lean_ctor_set(x_38, 2, x_16);
lean_ctor_set(x_38, 3, x_17);
lean_ctor_set(x_38, 4, x_18);
lean_ctor_set(x_38, 5, x_19);
lean_ctor_set(x_38, 6, x_20);
lean_ctor_set(x_38, 7, x_21);
lean_ctor_set(x_38, 8, x_22);
lean_ctor_set(x_38, 9, x_23);
lean_ctor_set(x_38, 10, x_27);
lean_ctor_set_uint8(x_38, sizeof(void*)*11, x_24);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 1, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*11 + 2, x_26);
x_39 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_29, x_38, x_30);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_27);
lean_dec(x_23);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
x_46 = lean_ctor_get(x_9, 2);
x_47 = lean_ctor_get(x_9, 3);
x_48 = lean_ctor_get(x_9, 4);
x_49 = lean_ctor_get(x_9, 5);
x_50 = lean_ctor_get(x_9, 6);
x_51 = lean_ctor_get(x_9, 7);
x_52 = lean_ctor_get(x_9, 8);
x_53 = lean_ctor_get(x_9, 9);
x_54 = lean_ctor_get_uint8(x_9, sizeof(void*)*11);
x_55 = lean_ctor_get_uint8(x_9, sizeof(void*)*11 + 1);
x_56 = lean_ctor_get_uint8(x_9, sizeof(void*)*11 + 2);
x_57 = lean_ctor_get(x_9, 10);
lean_inc(x_57);
lean_inc(x_53);
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
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_58 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_45);
lean_ctor_set(x_58, 2, x_46);
lean_ctor_set(x_58, 3, x_47);
lean_ctor_set(x_58, 4, x_48);
lean_ctor_set(x_58, 5, x_49);
lean_ctor_set(x_58, 6, x_50);
lean_ctor_set(x_58, 7, x_51);
lean_ctor_set(x_58, 8, x_52);
lean_ctor_set(x_58, 9, x_53);
lean_ctor_set(x_58, 10, x_1);
lean_ctor_set_uint8(x_58, sizeof(void*)*11, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*11 + 1, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*11 + 2, x_56);
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
x_67 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_67, 0, x_44);
lean_ctor_set(x_67, 1, x_45);
lean_ctor_set(x_67, 2, x_46);
lean_ctor_set(x_67, 3, x_47);
lean_ctor_set(x_67, 4, x_48);
lean_ctor_set(x_67, 5, x_49);
lean_ctor_set(x_67, 6, x_50);
lean_ctor_set(x_67, 7, x_51);
lean_ctor_set(x_67, 8, x_52);
lean_ctor_set(x_67, 9, x_53);
lean_ctor_set(x_67, 10, x_57);
lean_ctor_set_uint8(x_67, sizeof(void*)*11, x_54);
lean_ctor_set_uint8(x_67, sizeof(void*)*11 + 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*11 + 2, x_56);
x_68 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_60, x_67, x_61);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_69, 0, x_44);
lean_ctor_set(x_69, 1, x_45);
lean_ctor_set(x_69, 2, x_46);
lean_ctor_set(x_69, 3, x_47);
lean_ctor_set(x_69, 4, x_48);
lean_ctor_set(x_69, 5, x_49);
lean_ctor_set(x_69, 6, x_50);
lean_ctor_set(x_69, 7, x_51);
lean_ctor_set(x_69, 8, x_52);
lean_ctor_set(x_69, 9, x_53);
lean_ctor_set(x_69, 10, x_57);
lean_ctor_set_uint8(x_69, sizeof(void*)*11, x_54);
lean_ctor_set_uint8(x_69, sizeof(void*)*11 + 1, x_55);
lean_ctor_set_uint8(x_69, sizeof(void*)*11 + 2, x_56);
x_70 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_60, x_69, x_61);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_57);
lean_dec(x_53);
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
uint8_t x_10; 
x_10 = l_Lean_Syntax_isIdent(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_Syntax_getKind(x_1);
x_12 = l_Lean_choiceKind;
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_329; lean_object* x_437; uint8_t x_438; 
x_437 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_inc(x_1);
x_438 = l_Lean_Syntax_isOfKind(x_1, x_437);
if (x_438 == 0)
{
uint8_t x_439; 
x_439 = 0;
x_329 = x_439;
goto block_436;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; 
x_440 = l_Lean_Syntax_getArgs(x_1);
x_441 = lean_array_get_size(x_440);
lean_dec(x_440);
x_442 = lean_unsigned_to_nat(3u);
x_443 = lean_nat_dec_eq(x_441, x_442);
lean_dec(x_441);
x_329 = x_443;
goto block_436;
}
block_328:
{
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_314; uint8_t x_315; 
x_314 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_1);
x_315 = l_Lean_Syntax_isOfKind(x_1, x_314);
if (x_315 == 0)
{
uint8_t x_316; 
x_316 = 0;
x_15 = x_316;
goto block_313;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_317 = l_Lean_Syntax_getArgs(x_1);
x_318 = lean_array_get_size(x_317);
lean_dec(x_317);
x_319 = lean_unsigned_to_nat(2u);
x_320 = lean_nat_dec_eq(x_318, x_319);
lean_dec(x_318);
x_15 = x_320;
goto block_313;
}
block_313:
{
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_1);
x_17 = l_Lean_Syntax_isOfKind(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_box(0);
x_19 = 1;
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Elab_Term_elabTerm(x_1, x_18, x_19, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l___private_Lean_Elab_App_19__elabAppLVals(x_22, x_2, x_3, x_4, x_5, x_6, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_array_push(x_7, x_24);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_7, x_29);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_31);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
lean_ctor_set(x_24, 0, x_35);
x_36 = lean_array_push(x_7, x_24);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 0, x_36);
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_7, x_39);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 0, x_40);
return x_20;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_20);
lean_dec(x_9);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_24, 0);
lean_dec(x_42);
return x_24;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_dec(x_24);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_free_object(x_20);
lean_dec(x_7);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_24, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_24, 0);
lean_dec(x_47);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
else
{
lean_object* x_48; 
lean_dec(x_24);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_31);
lean_ctor_set(x_48, 1, x_9);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = l___private_Lean_Elab_App_19__elabAppLVals(x_49, x_2, x_3, x_4, x_5, x_6, x_8, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_array_push(x_7, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_9);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_array_push(x_7, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_9);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_9);
lean_dec(x_7);
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_67 = x_51;
} else {
 lean_dec_ref(x_51);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_7);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_69 = x_51;
} else {
 lean_dec_ref(x_51);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_9);
return x_70;
}
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_20, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
lean_dec(x_71);
x_73 = !lean_is_exclusive(x_20);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_20, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
lean_ctor_set(x_20, 0, x_75);
x_76 = lean_array_push(x_7, x_20);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_9);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_20, 1);
lean_inc(x_78);
lean_dec(x_20);
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_7, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_9);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_9);
lean_dec(x_7);
x_83 = !lean_is_exclusive(x_20);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_20, 0);
lean_dec(x_84);
return x_20;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_20, 1);
lean_inc(x_85);
lean_dec(x_20);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_71);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_7);
x_87 = !lean_is_exclusive(x_20);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_20, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_20, 0);
lean_dec(x_89);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_90; 
lean_dec(x_20);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_71);
lean_ctor_set(x_90, 1, x_9);
return x_90;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = l_Lean_Syntax_getArgs(x_1);
x_92 = lean_array_get_size(x_91);
lean_dec(x_91);
x_93 = lean_unsigned_to_nat(2u);
x_94 = lean_nat_dec_eq(x_92, x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_95 = lean_box(0);
x_96 = 1;
lean_inc(x_9);
lean_inc(x_8);
x_97 = l_Lean_Elab_Term_elabTerm(x_1, x_95, x_96, x_8, x_9);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
x_101 = l___private_Lean_Elab_App_19__elabAppLVals(x_99, x_2, x_3, x_4, x_5, x_6, x_8, x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_array_push(x_7, x_101);
lean_ctor_set(x_97, 1, x_9);
lean_ctor_set(x_97, 0, x_103);
return x_97;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_101, 0);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_101);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_push(x_7, x_106);
lean_ctor_set(x_97, 1, x_9);
lean_ctor_set(x_97, 0, x_107);
return x_97;
}
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
lean_dec(x_108);
x_110 = !lean_is_exclusive(x_101);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_101, 0);
lean_dec(x_111);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
lean_dec(x_109);
lean_ctor_set(x_101, 0, x_112);
x_113 = lean_array_push(x_7, x_101);
lean_ctor_set(x_97, 1, x_9);
lean_ctor_set(x_97, 0, x_113);
return x_97;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_dec(x_101);
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_array_push(x_7, x_116);
lean_ctor_set(x_97, 1, x_9);
lean_ctor_set(x_97, 0, x_117);
return x_97;
}
}
else
{
uint8_t x_118; 
lean_free_object(x_97);
lean_dec(x_9);
lean_dec(x_7);
x_118 = !lean_is_exclusive(x_101);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_101, 0);
lean_dec(x_119);
return x_101;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_101, 1);
lean_inc(x_120);
lean_dec(x_101);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_108);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_free_object(x_97);
lean_dec(x_7);
x_122 = !lean_is_exclusive(x_101);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_101, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_101, 0);
lean_dec(x_124);
lean_ctor_set(x_101, 1, x_9);
return x_101;
}
else
{
lean_object* x_125; 
lean_dec(x_101);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_108);
lean_ctor_set(x_125, 1, x_9);
return x_125;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_97, 0);
x_127 = lean_ctor_get(x_97, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_97);
x_128 = l___private_Lean_Elab_App_19__elabAppLVals(x_126, x_2, x_3, x_4, x_5, x_6, x_8, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_array_push(x_7, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_9);
return x_134;
}
else
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_128, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_135);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_138 = x_128;
} else {
 lean_dec_ref(x_128);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
lean_dec(x_136);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
x_141 = lean_array_push(x_7, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_9);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_9);
lean_dec(x_7);
x_143 = lean_ctor_get(x_128, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_144 = x_128;
} else {
 lean_dec_ref(x_128);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_7);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_146 = x_128;
} else {
 lean_dec_ref(x_128);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_135);
lean_ctor_set(x_147, 1, x_9);
return x_147;
}
}
}
}
else
{
lean_object* x_148; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_97, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
lean_dec(x_148);
x_150 = !lean_is_exclusive(x_97);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_97, 0);
lean_dec(x_151);
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
lean_dec(x_149);
lean_ctor_set(x_97, 0, x_152);
x_153 = lean_array_push(x_7, x_97);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_9);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_97, 1);
lean_inc(x_155);
lean_dec(x_97);
x_156 = lean_ctor_get(x_149, 0);
lean_inc(x_156);
lean_dec(x_149);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_array_push(x_7, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_9);
return x_159;
}
}
else
{
uint8_t x_160; 
lean_dec(x_9);
lean_dec(x_7);
x_160 = !lean_is_exclusive(x_97);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_97, 0);
lean_dec(x_161);
return x_97;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_97, 1);
lean_inc(x_162);
lean_dec(x_97);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_148);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_7);
x_164 = !lean_is_exclusive(x_97);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_97, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_97, 0);
lean_dec(x_166);
lean_ctor_set(x_97, 1, x_9);
return x_97;
}
else
{
lean_object* x_167; 
lean_dec(x_97);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_148);
lean_ctor_set(x_167, 1, x_9);
return x_167;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_168 = lean_unsigned_to_nat(1u);
x_169 = l_Lean_Syntax_getArg(x_1, x_168);
lean_dec(x_1);
x_170 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_169);
x_171 = l_Lean_Syntax_isOfKind(x_169, x_170);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_169);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_172 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_9);
return x_172;
}
else
{
uint8_t x_173; 
x_173 = 1;
x_1 = x_169;
x_6 = x_173;
goto _start;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_175 = lean_unsigned_to_nat(0u);
x_176 = l_Lean_Syntax_getArg(x_1, x_175);
x_177 = l_Lean_identKind___closed__2;
lean_inc(x_176);
x_178 = l_Lean_Syntax_isOfKind(x_176, x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; lean_object* x_181; 
lean_dec(x_176);
x_179 = lean_box(0);
x_180 = 1;
lean_inc(x_9);
lean_inc(x_8);
x_181 = l_Lean_Elab_Term_elabTerm(x_1, x_179, x_180, x_8, x_9);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_181, 0);
x_184 = lean_ctor_get(x_181, 1);
x_185 = l___private_Lean_Elab_App_19__elabAppLVals(x_183, x_2, x_3, x_4, x_5, x_6, x_8, x_184);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; 
x_187 = lean_array_push(x_7, x_185);
lean_ctor_set(x_181, 1, x_9);
lean_ctor_set(x_181, 0, x_187);
return x_181;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_185, 0);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_185);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_array_push(x_7, x_190);
lean_ctor_set(x_181, 1, x_9);
lean_ctor_set(x_181, 0, x_191);
return x_181;
}
}
else
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_185, 0);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
uint8_t x_194; 
lean_dec(x_192);
x_194 = !lean_is_exclusive(x_185);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_185, 0);
lean_dec(x_195);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
lean_dec(x_193);
lean_ctor_set(x_185, 0, x_196);
x_197 = lean_array_push(x_7, x_185);
lean_ctor_set(x_181, 1, x_9);
lean_ctor_set(x_181, 0, x_197);
return x_181;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_185, 1);
lean_inc(x_198);
lean_dec(x_185);
x_199 = lean_ctor_get(x_193, 0);
lean_inc(x_199);
lean_dec(x_193);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
x_201 = lean_array_push(x_7, x_200);
lean_ctor_set(x_181, 1, x_9);
lean_ctor_set(x_181, 0, x_201);
return x_181;
}
}
else
{
uint8_t x_202; 
lean_free_object(x_181);
lean_dec(x_9);
lean_dec(x_7);
x_202 = !lean_is_exclusive(x_185);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_185, 0);
lean_dec(x_203);
return x_185;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_185, 1);
lean_inc(x_204);
lean_dec(x_185);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_192);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_free_object(x_181);
lean_dec(x_7);
x_206 = !lean_is_exclusive(x_185);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_185, 1);
lean_dec(x_207);
x_208 = lean_ctor_get(x_185, 0);
lean_dec(x_208);
lean_ctor_set(x_185, 1, x_9);
return x_185;
}
else
{
lean_object* x_209; 
lean_dec(x_185);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_192);
lean_ctor_set(x_209, 1, x_9);
return x_209;
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_181, 0);
x_211 = lean_ctor_get(x_181, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_181);
x_212 = l___private_Lean_Elab_App_19__elabAppLVals(x_210, x_2, x_3, x_4, x_5, x_6, x_8, x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
x_217 = lean_array_push(x_7, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_9);
return x_218;
}
else
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_212, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_219);
x_221 = lean_ctor_get(x_212, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_222 = x_212;
} else {
 lean_dec_ref(x_212);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_220, 0);
lean_inc(x_223);
lean_dec(x_220);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
x_225 = lean_array_push(x_7, x_224);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_9);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_9);
lean_dec(x_7);
x_227 = lean_ctor_get(x_212, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_228 = x_212;
} else {
 lean_dec_ref(x_212);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_219);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_7);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_230 = x_212;
} else {
 lean_dec_ref(x_212);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_219);
lean_ctor_set(x_231, 1, x_9);
return x_231;
}
}
}
}
else
{
lean_object* x_232; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_232 = lean_ctor_get(x_181, 0);
lean_inc(x_232);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; 
lean_dec(x_232);
x_234 = !lean_is_exclusive(x_181);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_181, 0);
lean_dec(x_235);
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
lean_dec(x_233);
lean_ctor_set(x_181, 0, x_236);
x_237 = lean_array_push(x_7, x_181);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_9);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_239 = lean_ctor_get(x_181, 1);
lean_inc(x_239);
lean_dec(x_181);
x_240 = lean_ctor_get(x_233, 0);
lean_inc(x_240);
lean_dec(x_233);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_array_push(x_7, x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_9);
return x_243;
}
}
else
{
uint8_t x_244; 
lean_dec(x_9);
lean_dec(x_7);
x_244 = !lean_is_exclusive(x_181);
if (x_244 == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_181, 0);
lean_dec(x_245);
return x_181;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_181, 1);
lean_inc(x_246);
lean_dec(x_181);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_232);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_7);
x_248 = !lean_is_exclusive(x_181);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_181, 1);
lean_dec(x_249);
x_250 = lean_ctor_get(x_181, 0);
lean_dec(x_250);
lean_ctor_set(x_181, 1, x_9);
return x_181;
}
else
{
lean_object* x_251; 
lean_dec(x_181);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_232);
lean_ctor_set(x_251, 1, x_9);
return x_251;
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_307; uint8_t x_308; 
x_252 = lean_unsigned_to_nat(1u);
x_253 = l_Lean_Syntax_getArg(x_1, x_252);
lean_dec(x_1);
x_307 = l_Lean_nullKind___closed__2;
lean_inc(x_253);
x_308 = l_Lean_Syntax_isOfKind(x_253, x_307);
if (x_308 == 0)
{
uint8_t x_309; 
x_309 = 0;
x_254 = x_309;
goto block_306;
}
else
{
lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_310 = l_Lean_Syntax_getArgs(x_253);
x_311 = lean_array_get_size(x_310);
lean_dec(x_310);
x_312 = lean_nat_dec_eq(x_311, x_252);
lean_dec(x_311);
x_254 = x_312;
goto block_306;
}
block_306:
{
if (x_254 == 0)
{
lean_object* x_255; uint8_t x_256; 
x_255 = l_Lean_Syntax_getArgs(x_253);
lean_dec(x_253);
x_256 = l_Array_isEmpty___rarg(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = l_Lean_Syntax_inhabited;
x_258 = lean_array_get(x_257, x_255, x_175);
lean_dec(x_255);
x_259 = l_Lean_Elab_Term_elabExplicitUniv(x_258, x_8, x_9);
lean_dec(x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l___private_Lean_Elab_App_20__elabAppFnId(x_176, x_260, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_261);
return x_262;
}
else
{
uint8_t x_263; 
lean_dec(x_176);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_268 = l___private_Lean_Elab_App_20__elabAppFnId(x_176, x_267, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_269 = l_Lean_Syntax_getArg(x_253, x_175);
x_270 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
lean_inc(x_269);
x_271 = l_Lean_Syntax_isOfKind(x_269, x_270);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
lean_dec(x_269);
x_272 = l_Lean_Syntax_getArgs(x_253);
lean_dec(x_253);
x_273 = l_Array_isEmpty___rarg(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = l_Lean_Syntax_inhabited;
x_275 = lean_array_get(x_274, x_272, x_175);
lean_dec(x_272);
x_276 = l_Lean_Elab_Term_elabExplicitUniv(x_275, x_8, x_9);
lean_dec(x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = l___private_Lean_Elab_App_20__elabAppFnId(x_176, x_277, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_278);
return x_279;
}
else
{
uint8_t x_280; 
lean_dec(x_176);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_280 = !lean_is_exclusive(x_276);
if (x_280 == 0)
{
return x_276;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_276, 0);
x_282 = lean_ctor_get(x_276, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_276);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_272);
x_284 = lean_box(0);
x_285 = l___private_Lean_Elab_App_20__elabAppFnId(x_176, x_284, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_286 = l_Lean_Syntax_getArgs(x_269);
lean_dec(x_269);
x_287 = lean_array_get_size(x_286);
lean_dec(x_286);
x_288 = lean_unsigned_to_nat(2u);
x_289 = lean_nat_dec_eq(x_287, x_288);
lean_dec(x_287);
if (x_289 == 0)
{
lean_object* x_290; uint8_t x_291; 
x_290 = l_Lean_Syntax_getArgs(x_253);
lean_dec(x_253);
x_291 = l_Array_isEmpty___rarg(x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = l_Lean_Syntax_inhabited;
x_293 = lean_array_get(x_292, x_290, x_175);
lean_dec(x_290);
x_294 = l_Lean_Elab_Term_elabExplicitUniv(x_293, x_8, x_9);
lean_dec(x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_297 = l___private_Lean_Elab_App_20__elabAppFnId(x_176, x_295, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_296);
return x_297;
}
else
{
uint8_t x_298; 
lean_dec(x_176);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_298 = !lean_is_exclusive(x_294);
if (x_298 == 0)
{
return x_294;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_294, 0);
x_300 = lean_ctor_get(x_294, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_294);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_290);
x_302 = lean_box(0);
x_303 = l___private_Lean_Elab_App_20__elabAppFnId(x_176, x_302, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_253);
lean_dec(x_176);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_304 = l___private_Lean_Elab_App_21__elabAppFn___main___closed__3;
x_305 = l_Lean_Elab_Term_throwError___rarg(x_304, x_8, x_9);
return x_305;
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
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_321 = lean_unsigned_to_nat(0u);
x_322 = l_Lean_Syntax_getArg(x_1, x_321);
x_323 = lean_unsigned_to_nat(2u);
x_324 = l_Lean_Syntax_getArg(x_1, x_323);
lean_dec(x_1);
x_325 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_2);
x_1 = x_322;
x_2 = x_326;
goto _start;
}
}
block_436:
{
if (x_329 == 0)
{
lean_object* x_330; uint8_t x_331; 
x_330 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_inc(x_1);
x_331 = l_Lean_Syntax_isOfKind(x_1, x_330);
if (x_331 == 0)
{
uint8_t x_332; 
x_332 = 0;
x_14 = x_332;
goto block_328;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_333 = l_Lean_Syntax_getArgs(x_1);
x_334 = lean_array_get_size(x_333);
lean_dec(x_333);
x_335 = lean_unsigned_to_nat(4u);
x_336 = lean_nat_dec_eq(x_334, x_335);
lean_dec(x_334);
x_14 = x_336;
goto block_328;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_337 = lean_unsigned_to_nat(0u);
x_338 = l_Lean_Syntax_getArg(x_1, x_337);
x_339 = lean_unsigned_to_nat(2u);
x_340 = l_Lean_Syntax_getArg(x_1, x_339);
x_341 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_340);
x_342 = l_Lean_Syntax_isOfKind(x_340, x_341);
if (x_342 == 0)
{
lean_object* x_343; uint8_t x_344; 
x_343 = l_Lean_identKind___closed__2;
lean_inc(x_340);
x_344 = l_Lean_Syntax_isOfKind(x_340, x_343);
if (x_344 == 0)
{
lean_object* x_345; uint8_t x_346; lean_object* x_347; 
lean_dec(x_340);
lean_dec(x_338);
x_345 = lean_box(0);
x_346 = 1;
lean_inc(x_9);
lean_inc(x_8);
x_347 = l_Lean_Elab_Term_elabTerm(x_1, x_345, x_346, x_8, x_9);
if (lean_obj_tag(x_347) == 0)
{
uint8_t x_348; 
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_347, 0);
x_350 = lean_ctor_get(x_347, 1);
x_351 = l___private_Lean_Elab_App_19__elabAppLVals(x_349, x_2, x_3, x_4, x_5, x_6, x_8, x_350);
if (lean_obj_tag(x_351) == 0)
{
uint8_t x_352; 
x_352 = !lean_is_exclusive(x_351);
if (x_352 == 0)
{
lean_object* x_353; 
x_353 = lean_array_push(x_7, x_351);
lean_ctor_set(x_347, 1, x_9);
lean_ctor_set(x_347, 0, x_353);
return x_347;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_ctor_get(x_351, 0);
x_355 = lean_ctor_get(x_351, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_351);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
x_357 = lean_array_push(x_7, x_356);
lean_ctor_set(x_347, 1, x_9);
lean_ctor_set(x_347, 0, x_357);
return x_347;
}
}
else
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_351, 0);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
if (lean_obj_tag(x_359) == 0)
{
uint8_t x_360; 
lean_dec(x_358);
x_360 = !lean_is_exclusive(x_351);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_351, 0);
lean_dec(x_361);
x_362 = lean_ctor_get(x_359, 0);
lean_inc(x_362);
lean_dec(x_359);
lean_ctor_set(x_351, 0, x_362);
x_363 = lean_array_push(x_7, x_351);
lean_ctor_set(x_347, 1, x_9);
lean_ctor_set(x_347, 0, x_363);
return x_347;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_351, 1);
lean_inc(x_364);
lean_dec(x_351);
x_365 = lean_ctor_get(x_359, 0);
lean_inc(x_365);
lean_dec(x_359);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_364);
x_367 = lean_array_push(x_7, x_366);
lean_ctor_set(x_347, 1, x_9);
lean_ctor_set(x_347, 0, x_367);
return x_347;
}
}
else
{
uint8_t x_368; 
lean_free_object(x_347);
lean_dec(x_9);
lean_dec(x_7);
x_368 = !lean_is_exclusive(x_351);
if (x_368 == 0)
{
lean_object* x_369; 
x_369 = lean_ctor_get(x_351, 0);
lean_dec(x_369);
return x_351;
}
else
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_351, 1);
lean_inc(x_370);
lean_dec(x_351);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_358);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
}
else
{
uint8_t x_372; 
lean_free_object(x_347);
lean_dec(x_7);
x_372 = !lean_is_exclusive(x_351);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_351, 1);
lean_dec(x_373);
x_374 = lean_ctor_get(x_351, 0);
lean_dec(x_374);
lean_ctor_set(x_351, 1, x_9);
return x_351;
}
else
{
lean_object* x_375; 
lean_dec(x_351);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_358);
lean_ctor_set(x_375, 1, x_9);
return x_375;
}
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_347, 0);
x_377 = lean_ctor_get(x_347, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_347);
x_378 = l___private_Lean_Elab_App_19__elabAppLVals(x_376, x_2, x_3, x_4, x_5, x_6, x_8, x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_381 = x_378;
} else {
 lean_dec_ref(x_378);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
x_383 = lean_array_push(x_7, x_382);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_9);
return x_384;
}
else
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_378, 0);
lean_inc(x_385);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_385);
x_387 = lean_ctor_get(x_378, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_388 = x_378;
} else {
 lean_dec_ref(x_378);
 x_388 = lean_box(0);
}
x_389 = lean_ctor_get(x_386, 0);
lean_inc(x_389);
lean_dec(x_386);
if (lean_is_scalar(x_388)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_388;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_387);
x_391 = lean_array_push(x_7, x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_9);
return x_392;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_9);
lean_dec(x_7);
x_393 = lean_ctor_get(x_378, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_394 = x_378;
} else {
 lean_dec_ref(x_378);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_385);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_7);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_396 = x_378;
} else {
 lean_dec_ref(x_378);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_385);
lean_ctor_set(x_397, 1, x_9);
return x_397;
}
}
}
}
else
{
lean_object* x_398; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_398 = lean_ctor_get(x_347, 0);
lean_inc(x_398);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
uint8_t x_400; 
lean_dec(x_398);
x_400 = !lean_is_exclusive(x_347);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_401 = lean_ctor_get(x_347, 0);
lean_dec(x_401);
x_402 = lean_ctor_get(x_399, 0);
lean_inc(x_402);
lean_dec(x_399);
lean_ctor_set(x_347, 0, x_402);
x_403 = lean_array_push(x_7, x_347);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_9);
return x_404;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_405 = lean_ctor_get(x_347, 1);
lean_inc(x_405);
lean_dec(x_347);
x_406 = lean_ctor_get(x_399, 0);
lean_inc(x_406);
lean_dec(x_399);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_405);
x_408 = lean_array_push(x_7, x_407);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_9);
return x_409;
}
}
else
{
uint8_t x_410; 
lean_dec(x_9);
lean_dec(x_7);
x_410 = !lean_is_exclusive(x_347);
if (x_410 == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_347, 0);
lean_dec(x_411);
return x_347;
}
else
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_347, 1);
lean_inc(x_412);
lean_dec(x_347);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_398);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
}
else
{
uint8_t x_414; 
lean_dec(x_7);
x_414 = !lean_is_exclusive(x_347);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; 
x_415 = lean_ctor_get(x_347, 1);
lean_dec(x_415);
x_416 = lean_ctor_get(x_347, 0);
lean_dec(x_416);
lean_ctor_set(x_347, 1, x_9);
return x_347;
}
else
{
lean_object* x_417; 
lean_dec(x_347);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_398);
lean_ctor_set(x_417, 1, x_9);
return x_417;
}
}
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_1);
x_418 = l_Lean_Syntax_getId(x_340);
lean_dec(x_340);
x_419 = l_Lean_Name_eraseMacroScopes(x_418);
lean_dec(x_418);
x_420 = l_Lean_Name_components(x_419);
x_421 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__1(x_420);
x_422 = l_List_append___rarg(x_421, x_2);
x_1 = x_338;
x_2 = x_422;
goto _start;
}
}
else
{
lean_object* x_424; lean_object* x_425; 
lean_dec(x_1);
x_424 = l_Lean_fieldIdxKind;
x_425 = l_Lean_Syntax_isNatLitAux(x_424, x_340);
lean_dec(x_340);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_426 = l_Nat_Inhabited;
x_427 = l_Option_get_x21___rarg___closed__3;
x_428 = lean_panic_fn(x_426, x_427);
x_429 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_429, 0, x_428);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_2);
x_1 = x_338;
x_2 = x_430;
goto _start;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_425, 0);
lean_inc(x_432);
lean_dec(x_425);
x_433 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_433, 0, x_432);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_2);
x_1 = x_338;
x_2 = x_434;
goto _start;
}
}
}
}
}
else
{
lean_object* x_444; uint8_t x_445; 
x_444 = l_Lean_Syntax_getArgs(x_1);
x_445 = !lean_is_exclusive(x_8);
if (x_445 == 0)
{
uint8_t x_446; lean_object* x_447; lean_object* x_448; 
x_446 = 0;
lean_ctor_set_uint8(x_8, sizeof(void*)*11 + 1, x_446);
x_447 = lean_unsigned_to_nat(0u);
x_448 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_444, x_447, x_7, x_8, x_9);
lean_dec(x_444);
lean_dec(x_1);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_449 = lean_ctor_get(x_8, 0);
x_450 = lean_ctor_get(x_8, 1);
x_451 = lean_ctor_get(x_8, 2);
x_452 = lean_ctor_get(x_8, 3);
x_453 = lean_ctor_get(x_8, 4);
x_454 = lean_ctor_get(x_8, 5);
x_455 = lean_ctor_get(x_8, 6);
x_456 = lean_ctor_get(x_8, 7);
x_457 = lean_ctor_get(x_8, 8);
x_458 = lean_ctor_get(x_8, 9);
x_459 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_460 = lean_ctor_get_uint8(x_8, sizeof(void*)*11 + 2);
x_461 = lean_ctor_get(x_8, 10);
lean_inc(x_461);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_8);
x_462 = 0;
x_463 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_463, 0, x_449);
lean_ctor_set(x_463, 1, x_450);
lean_ctor_set(x_463, 2, x_451);
lean_ctor_set(x_463, 3, x_452);
lean_ctor_set(x_463, 4, x_453);
lean_ctor_set(x_463, 5, x_454);
lean_ctor_set(x_463, 6, x_455);
lean_ctor_set(x_463, 7, x_456);
lean_ctor_set(x_463, 8, x_457);
lean_ctor_set(x_463, 9, x_458);
lean_ctor_set(x_463, 10, x_461);
lean_ctor_set_uint8(x_463, sizeof(void*)*11, x_459);
lean_ctor_set_uint8(x_463, sizeof(void*)*11 + 1, x_462);
lean_ctor_set_uint8(x_463, sizeof(void*)*11 + 2, x_460);
x_464 = lean_unsigned_to_nat(0u);
x_465 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_444, x_464, x_7, x_463, x_9);
lean_dec(x_444);
lean_dec(x_1);
return x_465;
}
}
}
else
{
lean_object* x_466; lean_object* x_467; 
x_466 = lean_box(0);
x_467 = l___private_Lean_Elab_App_20__elabAppFnId(x_1, x_466, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_467;
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
x_5 = l_Lean_Elab_getPos___at_Lean_Elab_Term_throwErrorAt___spec__2(x_2, x_3, x_4);
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
x_14 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
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
x_15 = l_Lean_Elab_Term_throwErrorAt___rarg(x_2, x_14, x_3, x_11);
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
lean_object* x_21; 
lean_dec(x_17);
x_21 = l___private_Lean_Elab_App_24__mergeFailures___rarg(x_11, x_1, x_5, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
x_22 = l_Lean_Elab_Term_getLCtx(x_5, x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_getOptions(x_5, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = x_17;
x_29 = l_Array_umapMAux___main___at___private_Lean_Elab_App_25__elabAppAux___spec__1(x_23, x_26, x_16, x_28);
x_30 = x_29;
x_31 = l_Lean_MessageData_ofArray(x_30);
lean_dec(x_30);
x_32 = l___private_Lean_Elab_App_25__elabAppAux___closed__3;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_Term_throwErrorAt___rarg(x_1, x_33, x_5, x_27);
lean_dec(x_1);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_1);
x_35 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_36 = lean_array_get(x_35, x_17, x_16);
lean_dec(x_17);
x_37 = l_Lean_Elab_Term_applyResult(x_36, x_5, x_12);
lean_dec(x_12);
lean_dec(x_5);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_38 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_array_get(x_38, x_11, x_39);
lean_dec(x_11);
x_41 = l_Lean_Elab_Term_applyResult(x_40, x_5, x_12);
lean_dec(x_12);
lean_dec(x_5);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
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
x_45 = l_Lean_PrettyPrinter_Parenthesizer_termParser_parenthesizer___lambda__1___closed__2;
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
