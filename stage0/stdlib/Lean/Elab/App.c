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
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_getRefPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1(lean_object*, lean_object*);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__2;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__getSuccess(lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
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
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_16 = lean_ctor_get(x_4, 9);
x_17 = l_Lean_Elab_replaceRef(x_6, x_16);
lean_dec(x_16);
lean_ctor_set(x_4, 9, x_17);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_whnfForall(x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint64_t x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_19, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_19, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_19, 2);
lean_inc(x_95);
x_96 = lean_ctor_get_uint64(x_19, sizeof(void*)*3);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_93, x_11, x_97);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = (uint8_t)((x_96 << 24) >> 61);
switch (x_99) {
case 0:
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; uint8_t x_105; 
x_100 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_101 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_101, 0, x_6);
lean_ctor_set(x_101, 1, x_7);
lean_ctor_set(x_101, 2, x_8);
lean_ctor_set(x_101, 3, x_10);
lean_ctor_set(x_101, 4, x_11);
lean_ctor_set(x_101, 5, x_12);
lean_ctor_set(x_101, 6, x_13);
lean_ctor_set_uint8(x_101, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 1, x_100);
x_102 = lean_array_get_size(x_7);
x_103 = lean_nat_dec_lt(x_10, x_102);
lean_dec(x_102);
lean_inc(x_4);
lean_inc(x_1);
x_104 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_19, x_4, x_20);
x_105 = !lean_is_exclusive(x_1);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_1, 6);
lean_dec(x_106);
x_107 = lean_ctor_get(x_1, 5);
lean_dec(x_107);
x_108 = lean_ctor_get(x_1, 4);
lean_dec(x_108);
x_109 = lean_ctor_get(x_1, 3);
lean_dec(x_109);
x_110 = lean_ctor_get(x_1, 2);
lean_dec(x_110);
x_111 = lean_ctor_get(x_1, 1);
lean_dec(x_111);
x_112 = lean_ctor_get(x_1, 0);
lean_dec(x_112);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_104, 1);
lean_inc(x_113);
lean_dec(x_104);
if (x_103 == 0)
{
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_168; 
x_168 = l_Lean_Expr_getOptParamDefault_x3f(x_94);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = l_Lean_Expr_getAutoParamTactic_x3f(x_94);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_170 = lean_box(0);
x_114 = x_170;
goto block_167;
}
else
{
lean_object* x_171; 
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
if (lean_obj_tag(x_171) == 4)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec(x_171);
x_173 = l_Lean_Elab_Term_getEnv___rarg(x_113);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_174, x_172);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = l_Lean_Elab_Term_throwError___rarg(x_179, x_4, x_175);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_181 = lean_ctor_get(x_176, 0);
lean_inc(x_181);
lean_dec(x_176);
x_182 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_175);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Lean_Elab_Term_getMainModule___rarg(x_183);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = l_Lean_Syntax_getArgs(x_181);
lean_dec(x_181);
x_187 = l_Array_empty___closed__1;
x_188 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_186, x_186, x_97, x_187);
lean_dec(x_186);
x_189 = l_Lean_nullKind___closed__2;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_array_push(x_187, x_190);
x_192 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_195 = lean_array_push(x_194, x_193);
x_196 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_197 = lean_array_push(x_195, x_196);
x_198 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_201 = l_Lean_Expr_getAppNumArgsAux___main(x_94, x_97);
x_202 = lean_nat_sub(x_201, x_97);
lean_dec(x_201);
x_203 = lean_unsigned_to_nat(1u);
x_204 = lean_nat_sub(x_202, x_203);
lean_dec(x_202);
x_205 = l_Lean_Expr_getRevArg_x21___main(x_94, x_204);
lean_dec(x_94);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_199);
lean_inc(x_4);
lean_inc(x_2);
x_207 = l___private_Lean_Elab_App_2__elabArg(x_2, x_206, x_205, x_4, x_185);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
lean_inc(x_208);
x_210 = l_Lean_mkApp(x_2, x_208);
x_211 = lean_expr_instantiate1(x_95, x_208);
lean_dec(x_208);
lean_dec(x_95);
x_1 = x_101;
x_2 = x_210;
x_3 = x_211;
x_5 = x_209;
goto _start;
}
else
{
uint8_t x_213; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_213 = !lean_is_exclusive(x_207);
if (x_213 == 0)
{
return x_207;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_207, 0);
x_215 = lean_ctor_get(x_207, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_207);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_200, 0);
lean_inc(x_217);
lean_dec(x_200);
x_218 = l_Lean_Syntax_replaceInfo___main(x_217, x_199);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_218);
lean_inc(x_4);
lean_inc(x_2);
x_220 = l___private_Lean_Elab_App_2__elabArg(x_2, x_219, x_205, x_4, x_185);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
lean_inc(x_221);
x_223 = l_Lean_mkApp(x_2, x_221);
x_224 = lean_expr_instantiate1(x_95, x_221);
lean_dec(x_221);
lean_dec(x_95);
x_1 = x_101;
x_2 = x_223;
x_3 = x_224;
x_5 = x_222;
goto _start;
}
else
{
uint8_t x_226; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_226 = !lean_is_exclusive(x_220);
if (x_226 == 0)
{
return x_220;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_220, 0);
x_228 = lean_ctor_get(x_220, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_220);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_171);
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_230 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_231 = l_Lean_Elab_Term_throwError___rarg(x_230, x_4, x_113);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_232 = lean_ctor_get(x_168, 0);
lean_inc(x_232);
lean_dec(x_168);
lean_inc(x_232);
x_233 = l_Lean_mkApp(x_2, x_232);
x_234 = lean_expr_instantiate1(x_95, x_232);
lean_dec(x_232);
lean_dec(x_95);
x_1 = x_101;
x_2 = x_233;
x_3 = x_234;
x_5 = x_113;
goto _start;
}
}
else
{
lean_object* x_236; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_236 = lean_box(0);
x_114 = x_236;
goto block_167;
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_101);
lean_dec(x_93);
lean_dec(x_3);
x_237 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_238 = l___private_Lean_Elab_App_2__elabArg(x_2, x_237, x_94, x_4, x_113);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_add(x_10, x_241);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_242);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_100);
lean_inc(x_239);
x_243 = l_Lean_mkApp(x_2, x_239);
x_244 = lean_expr_instantiate1(x_95, x_239);
lean_dec(x_239);
lean_dec(x_95);
x_2 = x_243;
x_3 = x_244;
x_5 = x_240;
goto _start;
}
else
{
uint8_t x_246; 
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
x_246 = !lean_is_exclusive(x_238);
if (x_246 == 0)
{
return x_238;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_238, 0);
x_248 = lean_ctor_get(x_238, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_238);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
block_167:
{
uint8_t x_115; 
lean_dec(x_114);
x_115 = l_Array_isEmpty___rarg(x_11);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_116, 0, x_93);
x_117 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_120 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = x_11;
x_122 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_121);
x_123 = x_122;
x_124 = l_Array_toList___rarg(x_123);
lean_dec(x_123);
x_125 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_124);
x_126 = l_Array_HasRepr___rarg___closed__1;
x_127 = lean_string_append(x_126, x_125);
lean_dec(x_125);
x_128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_130, 0, x_120);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Elab_Term_throwError___rarg(x_130, x_4, x_113);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_93);
lean_dec(x_11);
x_159 = l_Lean_Elab_Term_getOptions(x_4, x_113);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_163 = l_Lean_checkTraceOption(x_160, x_162);
lean_dec(x_160);
if (x_163 == 0)
{
x_132 = x_161;
goto block_158;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_inc(x_2);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_2);
x_165 = l_Lean_Elab_Term_logTrace(x_162, x_164, x_4, x_161);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_132 = x_166;
goto block_158;
}
block_158:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_133; 
lean_dec(x_3);
x_133 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_132);
lean_dec(x_12);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_133, 0);
lean_dec(x_135);
lean_ctor_set(x_133, 0, x_2);
return x_133;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_2);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
else
{
uint8_t x_138; 
lean_dec(x_2);
x_138 = !lean_is_exclusive(x_133);
if (x_138 == 0)
{
return x_133;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_133, 0);
x_140 = lean_ctor_get(x_133, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_133);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_8, 0);
lean_inc(x_142);
lean_dec(x_8);
lean_inc(x_4);
x_143 = l_Lean_Elab_Term_isDefEq(x_142, x_3, x_4, x_132);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_144);
lean_dec(x_12);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_145, 0);
lean_dec(x_147);
lean_ctor_set(x_145, 0, x_2);
return x_145;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_2);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_2);
x_150 = !lean_is_exclusive(x_145);
if (x_150 == 0)
{
return x_145;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_145, 0);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_145);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_154 = !lean_is_exclusive(x_143);
if (x_154 == 0)
{
return x_143;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_143, 0);
x_156 = lean_ctor_get(x_143, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_143);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
}
}
}
else
{
uint8_t x_250; 
lean_free_object(x_1);
lean_dec(x_101);
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
x_250 = !lean_is_exclusive(x_104);
if (x_250 == 0)
{
return x_104;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_104, 0);
x_252 = lean_ctor_get(x_104, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_104);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_104, 1);
lean_inc(x_254);
lean_dec(x_104);
if (x_103 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_307; 
x_307 = l_Lean_Expr_getOptParamDefault_x3f(x_94);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = l_Lean_Expr_getAutoParamTactic_x3f(x_94);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_309 = lean_box(0);
x_255 = x_309;
goto block_306;
}
else
{
lean_object* x_310; 
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
lean_dec(x_308);
if (lean_obj_tag(x_310) == 4)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
lean_dec(x_310);
x_312 = l_Lean_Elab_Term_getEnv___rarg(x_254);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_313, x_311);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec(x_315);
x_317 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_319 = l_Lean_Elab_Term_throwError___rarg(x_318, x_4, x_314);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_320 = lean_ctor_get(x_315, 0);
lean_inc(x_320);
lean_dec(x_315);
x_321 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_314);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
x_323 = l_Lean_Elab_Term_getMainModule___rarg(x_322);
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
lean_dec(x_323);
x_325 = l_Lean_Syntax_getArgs(x_320);
lean_dec(x_320);
x_326 = l_Array_empty___closed__1;
x_327 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_325, x_325, x_97, x_326);
lean_dec(x_325);
x_328 = l_Lean_nullKind___closed__2;
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
x_330 = lean_array_push(x_326, x_329);
x_331 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_330);
x_333 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_334 = lean_array_push(x_333, x_332);
x_335 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_336 = lean_array_push(x_334, x_335);
x_337 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_336);
x_339 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_340 = l_Lean_Expr_getAppNumArgsAux___main(x_94, x_97);
x_341 = lean_nat_sub(x_340, x_97);
lean_dec(x_340);
x_342 = lean_unsigned_to_nat(1u);
x_343 = lean_nat_sub(x_341, x_342);
lean_dec(x_341);
x_344 = l_Lean_Expr_getRevArg_x21___main(x_94, x_343);
lean_dec(x_94);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_345, 0, x_338);
lean_inc(x_4);
lean_inc(x_2);
x_346 = l___private_Lean_Elab_App_2__elabArg(x_2, x_345, x_344, x_4, x_324);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
lean_inc(x_347);
x_349 = l_Lean_mkApp(x_2, x_347);
x_350 = lean_expr_instantiate1(x_95, x_347);
lean_dec(x_347);
lean_dec(x_95);
x_1 = x_101;
x_2 = x_349;
x_3 = x_350;
x_5 = x_348;
goto _start;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_352 = lean_ctor_get(x_346, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_346, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_354 = x_346;
} else {
 lean_dec_ref(x_346);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_356 = lean_ctor_get(x_339, 0);
lean_inc(x_356);
lean_dec(x_339);
x_357 = l_Lean_Syntax_replaceInfo___main(x_356, x_338);
x_358 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_358, 0, x_357);
lean_inc(x_4);
lean_inc(x_2);
x_359 = l___private_Lean_Elab_App_2__elabArg(x_2, x_358, x_344, x_4, x_324);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
lean_inc(x_360);
x_362 = l_Lean_mkApp(x_2, x_360);
x_363 = lean_expr_instantiate1(x_95, x_360);
lean_dec(x_360);
lean_dec(x_95);
x_1 = x_101;
x_2 = x_362;
x_3 = x_363;
x_5 = x_361;
goto _start;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_365 = lean_ctor_get(x_359, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_359, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_367 = x_359;
} else {
 lean_dec_ref(x_359);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
}
}
else
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_310);
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_369 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_370 = l_Lean_Elab_Term_throwError___rarg(x_369, x_4, x_254);
return x_370;
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_371 = lean_ctor_get(x_307, 0);
lean_inc(x_371);
lean_dec(x_307);
lean_inc(x_371);
x_372 = l_Lean_mkApp(x_2, x_371);
x_373 = lean_expr_instantiate1(x_95, x_371);
lean_dec(x_371);
lean_dec(x_95);
x_1 = x_101;
x_2 = x_372;
x_3 = x_373;
x_5 = x_254;
goto _start;
}
}
else
{
lean_object* x_375; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_375 = lean_box(0);
x_255 = x_375;
goto block_306;
}
}
else
{
lean_object* x_376; lean_object* x_377; 
lean_dec(x_101);
lean_dec(x_93);
lean_dec(x_3);
x_376 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_377 = l___private_Lean_Elab_App_2__elabArg(x_2, x_376, x_94, x_4, x_254);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_unsigned_to_nat(1u);
x_381 = lean_nat_add(x_10, x_380);
lean_dec(x_10);
x_382 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_382, 0, x_6);
lean_ctor_set(x_382, 1, x_7);
lean_ctor_set(x_382, 2, x_8);
lean_ctor_set(x_382, 3, x_381);
lean_ctor_set(x_382, 4, x_11);
lean_ctor_set(x_382, 5, x_12);
lean_ctor_set(x_382, 6, x_13);
lean_ctor_set_uint8(x_382, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_382, sizeof(void*)*7 + 1, x_100);
lean_inc(x_378);
x_383 = l_Lean_mkApp(x_2, x_378);
x_384 = lean_expr_instantiate1(x_95, x_378);
lean_dec(x_378);
lean_dec(x_95);
x_1 = x_382;
x_2 = x_383;
x_3 = x_384;
x_5 = x_379;
goto _start;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
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
x_386 = lean_ctor_get(x_377, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_377, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_388 = x_377;
} else {
 lean_dec_ref(x_377);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
block_306:
{
uint8_t x_256; 
lean_dec(x_255);
x_256 = l_Array_isEmpty___rarg(x_11);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_257 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_257, 0, x_93);
x_258 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_259 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_261 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
x_262 = x_11;
x_263 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_262);
x_264 = x_263;
x_265 = l_Array_toList___rarg(x_264);
lean_dec(x_264);
x_266 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_265);
x_267 = l_Array_HasRepr___rarg___closed__1;
x_268 = lean_string_append(x_267, x_266);
lean_dec(x_266);
x_269 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_270, 0, x_269);
x_271 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_271, 0, x_261);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_Elab_Term_throwError___rarg(x_271, x_4, x_254);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
lean_dec(x_93);
lean_dec(x_11);
x_298 = l_Lean_Elab_Term_getOptions(x_4, x_254);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_302 = l_Lean_checkTraceOption(x_299, x_301);
lean_dec(x_299);
if (x_302 == 0)
{
x_273 = x_300;
goto block_297;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_inc(x_2);
x_303 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_303, 0, x_2);
x_304 = l_Lean_Elab_Term_logTrace(x_301, x_303, x_4, x_300);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
x_273 = x_305;
goto block_297;
}
block_297:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_274; 
lean_dec(x_3);
x_274 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_273);
lean_dec(x_12);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_2);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_2);
x_278 = lean_ctor_get(x_274, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_274, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_280 = x_274;
} else {
 lean_dec_ref(x_274);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_8, 0);
lean_inc(x_282);
lean_dec(x_8);
lean_inc(x_4);
x_283 = l_Lean_Elab_Term_isDefEq(x_282, x_3, x_4, x_273);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec(x_283);
x_285 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_284);
lean_dec(x_12);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_2);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_2);
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_285, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_291 = x_285;
} else {
 lean_dec_ref(x_285);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_293 = lean_ctor_get(x_283, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_283, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_295 = x_283;
} else {
 lean_dec_ref(x_283);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
}
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_101);
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
x_390 = lean_ctor_get(x_104, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_104, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_392 = x_104;
} else {
 lean_dec_ref(x_104);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
}
}
case 1:
{
if (x_9 == 0)
{
uint8_t x_394; 
lean_dec(x_93);
lean_dec(x_19);
lean_dec(x_3);
x_394 = !lean_is_exclusive(x_1);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_395 = lean_ctor_get(x_1, 6);
lean_dec(x_395);
x_396 = lean_ctor_get(x_1, 5);
lean_dec(x_396);
x_397 = lean_ctor_get(x_1, 4);
lean_dec(x_397);
x_398 = lean_ctor_get(x_1, 3);
lean_dec(x_398);
x_399 = lean_ctor_get(x_1, 2);
lean_dec(x_399);
x_400 = lean_ctor_get(x_1, 1);
lean_dec(x_400);
x_401 = lean_ctor_get(x_1, 0);
lean_dec(x_401);
x_402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_402, 0, x_94);
x_403 = 0;
x_404 = lean_box(0);
lean_inc(x_4);
x_405 = l_Lean_Elab_Term_mkFreshExprMVar(x_402, x_403, x_404, x_4, x_20);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
lean_inc(x_4);
lean_inc(x_406);
x_408 = l_Lean_Elab_Term_isTypeFormer(x_406, x_4, x_407);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; uint8_t x_410; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_unbox(x_409);
lean_dec(x_409);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_408, 1);
lean_inc(x_411);
lean_dec(x_408);
lean_inc(x_406);
x_412 = l_Lean_mkApp(x_2, x_406);
x_413 = lean_expr_instantiate1(x_95, x_406);
lean_dec(x_406);
lean_dec(x_95);
x_2 = x_412;
x_3 = x_413;
x_5 = x_411;
goto _start;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_415 = lean_ctor_get(x_408, 1);
lean_inc(x_415);
lean_dec(x_408);
x_416 = l_Lean_Expr_mvarId_x21(x_406);
x_417 = lean_array_push(x_13, x_416);
lean_ctor_set(x_1, 6, x_417);
lean_inc(x_406);
x_418 = l_Lean_mkApp(x_2, x_406);
x_419 = lean_expr_instantiate1(x_95, x_406);
lean_dec(x_406);
lean_dec(x_95);
x_2 = x_418;
x_3 = x_419;
x_5 = x_415;
goto _start;
}
}
else
{
uint8_t x_421; 
lean_dec(x_406);
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
x_421 = !lean_is_exclusive(x_408);
if (x_421 == 0)
{
return x_408;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_408, 0);
x_423 = lean_ctor_get(x_408, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_408);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
else
{
lean_object* x_425; uint8_t x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_1);
x_425 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_425, 0, x_94);
x_426 = 0;
x_427 = lean_box(0);
lean_inc(x_4);
x_428 = l_Lean_Elab_Term_mkFreshExprMVar(x_425, x_426, x_427, x_4, x_20);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
lean_inc(x_4);
lean_inc(x_429);
x_431 = l_Lean_Elab_Term_isTypeFormer(x_429, x_4, x_430);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_unbox(x_432);
lean_dec(x_432);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
lean_dec(x_431);
x_435 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_435, 0, x_6);
lean_ctor_set(x_435, 1, x_7);
lean_ctor_set(x_435, 2, x_8);
lean_ctor_set(x_435, 3, x_10);
lean_ctor_set(x_435, 4, x_11);
lean_ctor_set(x_435, 5, x_12);
lean_ctor_set(x_435, 6, x_13);
lean_ctor_set_uint8(x_435, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_435, sizeof(void*)*7 + 1, x_15);
lean_inc(x_429);
x_436 = l_Lean_mkApp(x_2, x_429);
x_437 = lean_expr_instantiate1(x_95, x_429);
lean_dec(x_429);
lean_dec(x_95);
x_1 = x_435;
x_2 = x_436;
x_3 = x_437;
x_5 = x_434;
goto _start;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_439 = lean_ctor_get(x_431, 1);
lean_inc(x_439);
lean_dec(x_431);
x_440 = l_Lean_Expr_mvarId_x21(x_429);
x_441 = lean_array_push(x_13, x_440);
x_442 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_442, 0, x_6);
lean_ctor_set(x_442, 1, x_7);
lean_ctor_set(x_442, 2, x_8);
lean_ctor_set(x_442, 3, x_10);
lean_ctor_set(x_442, 4, x_11);
lean_ctor_set(x_442, 5, x_12);
lean_ctor_set(x_442, 6, x_441);
lean_ctor_set_uint8(x_442, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_442, sizeof(void*)*7 + 1, x_15);
lean_inc(x_429);
x_443 = l_Lean_mkApp(x_2, x_429);
x_444 = lean_expr_instantiate1(x_95, x_429);
lean_dec(x_429);
lean_dec(x_95);
x_1 = x_442;
x_2 = x_443;
x_3 = x_444;
x_5 = x_439;
goto _start;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_429);
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
x_446 = lean_ctor_get(x_431, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_431, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_448 = x_431;
} else {
 lean_dec_ref(x_431);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
else
{
lean_object* x_450; uint8_t x_451; lean_object* x_452; uint8_t x_453; 
x_450 = lean_array_get_size(x_7);
x_451 = lean_nat_dec_lt(x_10, x_450);
lean_dec(x_450);
lean_inc(x_4);
lean_inc(x_1);
x_452 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_19, x_4, x_20);
x_453 = !lean_is_exclusive(x_1);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_454 = lean_ctor_get(x_1, 6);
lean_dec(x_454);
x_455 = lean_ctor_get(x_1, 5);
lean_dec(x_455);
x_456 = lean_ctor_get(x_1, 4);
lean_dec(x_456);
x_457 = lean_ctor_get(x_1, 3);
lean_dec(x_457);
x_458 = lean_ctor_get(x_1, 2);
lean_dec(x_458);
x_459 = lean_ctor_get(x_1, 1);
lean_dec(x_459);
x_460 = lean_ctor_get(x_1, 0);
lean_dec(x_460);
if (lean_obj_tag(x_452) == 0)
{
if (x_451 == 0)
{
lean_object* x_461; uint8_t x_462; 
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_461 = lean_ctor_get(x_452, 1);
lean_inc(x_461);
lean_dec(x_452);
x_462 = l_Array_isEmpty___rarg(x_11);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_463 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_463, 0, x_93);
x_464 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_465 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
x_466 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_467 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
x_468 = x_11;
x_469 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_468);
x_470 = x_469;
x_471 = l_Array_toList___rarg(x_470);
lean_dec(x_470);
x_472 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_471);
x_473 = l_Array_HasRepr___rarg___closed__1;
x_474 = lean_string_append(x_473, x_472);
lean_dec(x_472);
x_475 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_475, 0, x_474);
x_476 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_476, 0, x_475);
x_477 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_477, 0, x_467);
lean_ctor_set(x_477, 1, x_476);
x_478 = l_Lean_Elab_Term_throwError___rarg(x_477, x_4, x_461);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; 
lean_dec(x_93);
lean_dec(x_11);
x_506 = l_Lean_Elab_Term_getOptions(x_4, x_461);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_510 = l_Lean_checkTraceOption(x_507, x_509);
lean_dec(x_507);
if (x_510 == 0)
{
x_479 = x_508;
goto block_505;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_inc(x_2);
x_511 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_511, 0, x_2);
x_512 = l_Lean_Elab_Term_logTrace(x_509, x_511, x_4, x_508);
x_513 = lean_ctor_get(x_512, 1);
lean_inc(x_513);
lean_dec(x_512);
x_479 = x_513;
goto block_505;
}
block_505:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_480; 
lean_dec(x_3);
x_480 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_479);
lean_dec(x_12);
if (lean_obj_tag(x_480) == 0)
{
uint8_t x_481; 
x_481 = !lean_is_exclusive(x_480);
if (x_481 == 0)
{
lean_object* x_482; 
x_482 = lean_ctor_get(x_480, 0);
lean_dec(x_482);
lean_ctor_set(x_480, 0, x_2);
return x_480;
}
else
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
lean_dec(x_480);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_2);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
else
{
uint8_t x_485; 
lean_dec(x_2);
x_485 = !lean_is_exclusive(x_480);
if (x_485 == 0)
{
return x_480;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_480, 0);
x_487 = lean_ctor_get(x_480, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_480);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
}
else
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_ctor_get(x_8, 0);
lean_inc(x_489);
lean_dec(x_8);
lean_inc(x_4);
x_490 = l_Lean_Elab_Term_isDefEq(x_489, x_3, x_4, x_479);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_490, 1);
lean_inc(x_491);
lean_dec(x_490);
x_492 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_491);
lean_dec(x_12);
if (lean_obj_tag(x_492) == 0)
{
uint8_t x_493; 
x_493 = !lean_is_exclusive(x_492);
if (x_493 == 0)
{
lean_object* x_494; 
x_494 = lean_ctor_get(x_492, 0);
lean_dec(x_494);
lean_ctor_set(x_492, 0, x_2);
return x_492;
}
else
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_492, 1);
lean_inc(x_495);
lean_dec(x_492);
x_496 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_496, 0, x_2);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
else
{
uint8_t x_497; 
lean_dec(x_2);
x_497 = !lean_is_exclusive(x_492);
if (x_497 == 0)
{
return x_492;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_492, 0);
x_499 = lean_ctor_get(x_492, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_492);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
}
else
{
uint8_t x_501; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_501 = !lean_is_exclusive(x_490);
if (x_501 == 0)
{
return x_490;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_490, 0);
x_503 = lean_ctor_get(x_490, 1);
lean_inc(x_503);
lean_inc(x_502);
lean_dec(x_490);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
}
}
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_93);
lean_dec(x_3);
x_514 = lean_ctor_get(x_452, 1);
lean_inc(x_514);
lean_dec(x_452);
x_515 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_516 = l___private_Lean_Elab_App_2__elabArg(x_2, x_515, x_94, x_4, x_514);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; lean_object* x_522; lean_object* x_523; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
lean_dec(x_516);
x_519 = lean_unsigned_to_nat(1u);
x_520 = lean_nat_add(x_10, x_519);
lean_dec(x_10);
x_521 = 1;
lean_ctor_set(x_1, 3, x_520);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_521);
lean_inc(x_517);
x_522 = l_Lean_mkApp(x_2, x_517);
x_523 = lean_expr_instantiate1(x_95, x_517);
lean_dec(x_517);
lean_dec(x_95);
x_2 = x_522;
x_3 = x_523;
x_5 = x_518;
goto _start;
}
else
{
uint8_t x_525; 
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
x_525 = !lean_is_exclusive(x_516);
if (x_525 == 0)
{
return x_516;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_516, 0);
x_527 = lean_ctor_get(x_516, 1);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_516);
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
return x_528;
}
}
}
}
else
{
uint8_t x_529; 
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
x_529 = !lean_is_exclusive(x_452);
if (x_529 == 0)
{
return x_452;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_452, 0);
x_531 = lean_ctor_get(x_452, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_452);
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_452) == 0)
{
if (x_451 == 0)
{
lean_object* x_533; uint8_t x_534; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_533 = lean_ctor_get(x_452, 1);
lean_inc(x_533);
lean_dec(x_452);
x_534 = l_Array_isEmpty___rarg(x_11);
if (x_534 == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_535 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_535, 0, x_93);
x_536 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_537 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_535);
x_538 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_539 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
x_540 = x_11;
x_541 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_540);
x_542 = x_541;
x_543 = l_Array_toList___rarg(x_542);
lean_dec(x_542);
x_544 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_543);
x_545 = l_Array_HasRepr___rarg___closed__1;
x_546 = lean_string_append(x_545, x_544);
lean_dec(x_544);
x_547 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_547, 0, x_546);
x_548 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_548, 0, x_547);
x_549 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_549, 0, x_539);
lean_ctor_set(x_549, 1, x_548);
x_550 = l_Lean_Elab_Term_throwError___rarg(x_549, x_4, x_533);
return x_550;
}
else
{
lean_object* x_551; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; 
lean_dec(x_93);
lean_dec(x_11);
x_576 = l_Lean_Elab_Term_getOptions(x_4, x_533);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_579 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_580 = l_Lean_checkTraceOption(x_577, x_579);
lean_dec(x_577);
if (x_580 == 0)
{
x_551 = x_578;
goto block_575;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_inc(x_2);
x_581 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_581, 0, x_2);
x_582 = l_Lean_Elab_Term_logTrace(x_579, x_581, x_4, x_578);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
lean_dec(x_582);
x_551 = x_583;
goto block_575;
}
block_575:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_552; 
lean_dec(x_3);
x_552 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_551);
lean_dec(x_12);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_552, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_554 = x_552;
} else {
 lean_dec_ref(x_552);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_554)) {
 x_555 = lean_alloc_ctor(0, 2, 0);
} else {
 x_555 = x_554;
}
lean_ctor_set(x_555, 0, x_2);
lean_ctor_set(x_555, 1, x_553);
return x_555;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_2);
x_556 = lean_ctor_get(x_552, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_552, 1);
lean_inc(x_557);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 x_558 = x_552;
} else {
 lean_dec_ref(x_552);
 x_558 = lean_box(0);
}
if (lean_is_scalar(x_558)) {
 x_559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_559 = x_558;
}
lean_ctor_set(x_559, 0, x_556);
lean_ctor_set(x_559, 1, x_557);
return x_559;
}
}
else
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_8, 0);
lean_inc(x_560);
lean_dec(x_8);
lean_inc(x_4);
x_561 = l_Lean_Elab_Term_isDefEq(x_560, x_3, x_4, x_551);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; 
x_562 = lean_ctor_get(x_561, 1);
lean_inc(x_562);
lean_dec(x_561);
x_563 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_562);
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
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_571 = lean_ctor_get(x_561, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_561, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_573 = x_561;
} else {
 lean_dec_ref(x_561);
 x_573 = lean_box(0);
}
if (lean_is_scalar(x_573)) {
 x_574 = lean_alloc_ctor(1, 2, 0);
} else {
 x_574 = x_573;
}
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_572);
return x_574;
}
}
}
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
lean_dec(x_93);
lean_dec(x_3);
x_584 = lean_ctor_get(x_452, 1);
lean_inc(x_584);
lean_dec(x_452);
x_585 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_586 = l___private_Lean_Elab_App_2__elabArg(x_2, x_585, x_94, x_4, x_584);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
x_589 = lean_unsigned_to_nat(1u);
x_590 = lean_nat_add(x_10, x_589);
lean_dec(x_10);
x_591 = 1;
x_592 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_592, 0, x_6);
lean_ctor_set(x_592, 1, x_7);
lean_ctor_set(x_592, 2, x_8);
lean_ctor_set(x_592, 3, x_590);
lean_ctor_set(x_592, 4, x_11);
lean_ctor_set(x_592, 5, x_12);
lean_ctor_set(x_592, 6, x_13);
lean_ctor_set_uint8(x_592, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_592, sizeof(void*)*7 + 1, x_591);
lean_inc(x_587);
x_593 = l_Lean_mkApp(x_2, x_587);
x_594 = lean_expr_instantiate1(x_95, x_587);
lean_dec(x_587);
lean_dec(x_95);
x_1 = x_592;
x_2 = x_593;
x_3 = x_594;
x_5 = x_588;
goto _start;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
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
x_596 = lean_ctor_get(x_586, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_586, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_598 = x_586;
} else {
 lean_dec_ref(x_586);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_596);
lean_ctor_set(x_599, 1, x_597);
return x_599;
}
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
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
x_600 = lean_ctor_get(x_452, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_452, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_602 = x_452;
} else {
 lean_dec_ref(x_452);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_600);
lean_ctor_set(x_603, 1, x_601);
return x_603;
}
}
}
}
case 2:
{
uint8_t x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; lean_object* x_608; uint8_t x_609; 
x_604 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_605 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_605, 0, x_6);
lean_ctor_set(x_605, 1, x_7);
lean_ctor_set(x_605, 2, x_8);
lean_ctor_set(x_605, 3, x_10);
lean_ctor_set(x_605, 4, x_11);
lean_ctor_set(x_605, 5, x_12);
lean_ctor_set(x_605, 6, x_13);
lean_ctor_set_uint8(x_605, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_605, sizeof(void*)*7 + 1, x_604);
x_606 = lean_array_get_size(x_7);
x_607 = lean_nat_dec_lt(x_10, x_606);
lean_dec(x_606);
lean_inc(x_4);
lean_inc(x_1);
x_608 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_19, x_4, x_20);
x_609 = !lean_is_exclusive(x_1);
if (x_609 == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_610 = lean_ctor_get(x_1, 6);
lean_dec(x_610);
x_611 = lean_ctor_get(x_1, 5);
lean_dec(x_611);
x_612 = lean_ctor_get(x_1, 4);
lean_dec(x_612);
x_613 = lean_ctor_get(x_1, 3);
lean_dec(x_613);
x_614 = lean_ctor_get(x_1, 2);
lean_dec(x_614);
x_615 = lean_ctor_get(x_1, 1);
lean_dec(x_615);
x_616 = lean_ctor_get(x_1, 0);
lean_dec(x_616);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_617; lean_object* x_618; 
x_617 = lean_ctor_get(x_608, 1);
lean_inc(x_617);
lean_dec(x_608);
if (x_607 == 0)
{
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_672; 
x_672 = l_Lean_Expr_getOptParamDefault_x3f(x_94);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; 
x_673 = l_Lean_Expr_getAutoParamTactic_x3f(x_94);
if (lean_obj_tag(x_673) == 0)
{
lean_object* x_674; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_674 = lean_box(0);
x_618 = x_674;
goto block_671;
}
else
{
lean_object* x_675; 
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_675 = lean_ctor_get(x_673, 0);
lean_inc(x_675);
lean_dec(x_673);
if (lean_obj_tag(x_675) == 4)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
lean_dec(x_675);
x_677 = l_Lean_Elab_Term_getEnv___rarg(x_617);
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_677, 1);
lean_inc(x_679);
lean_dec(x_677);
x_680 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_678, x_676);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
lean_dec(x_680);
x_682 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_682, 0, x_681);
x_683 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_683, 0, x_682);
x_684 = l_Lean_Elab_Term_throwError___rarg(x_683, x_4, x_679);
return x_684;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_685 = lean_ctor_get(x_680, 0);
lean_inc(x_685);
lean_dec(x_680);
x_686 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_679);
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
lean_dec(x_686);
x_688 = l_Lean_Elab_Term_getMainModule___rarg(x_687);
x_689 = lean_ctor_get(x_688, 1);
lean_inc(x_689);
lean_dec(x_688);
x_690 = l_Lean_Syntax_getArgs(x_685);
lean_dec(x_685);
x_691 = l_Array_empty___closed__1;
x_692 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_690, x_690, x_97, x_691);
lean_dec(x_690);
x_693 = l_Lean_nullKind___closed__2;
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_692);
x_695 = lean_array_push(x_691, x_694);
x_696 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_695);
x_698 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_699 = lean_array_push(x_698, x_697);
x_700 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_701 = lean_array_push(x_699, x_700);
x_702 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_701);
x_704 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_705 = l_Lean_Expr_getAppNumArgsAux___main(x_94, x_97);
x_706 = lean_nat_sub(x_705, x_97);
lean_dec(x_705);
x_707 = lean_unsigned_to_nat(1u);
x_708 = lean_nat_sub(x_706, x_707);
lean_dec(x_706);
x_709 = l_Lean_Expr_getRevArg_x21___main(x_94, x_708);
lean_dec(x_94);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_710; lean_object* x_711; 
x_710 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_710, 0, x_703);
lean_inc(x_4);
lean_inc(x_2);
x_711 = l___private_Lean_Elab_App_2__elabArg(x_2, x_710, x_709, x_4, x_689);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec(x_711);
lean_inc(x_712);
x_714 = l_Lean_mkApp(x_2, x_712);
x_715 = lean_expr_instantiate1(x_95, x_712);
lean_dec(x_712);
lean_dec(x_95);
x_1 = x_605;
x_2 = x_714;
x_3 = x_715;
x_5 = x_713;
goto _start;
}
else
{
uint8_t x_717; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_717 = !lean_is_exclusive(x_711);
if (x_717 == 0)
{
return x_711;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_711, 0);
x_719 = lean_ctor_get(x_711, 1);
lean_inc(x_719);
lean_inc(x_718);
lean_dec(x_711);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
return x_720;
}
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_721 = lean_ctor_get(x_704, 0);
lean_inc(x_721);
lean_dec(x_704);
x_722 = l_Lean_Syntax_replaceInfo___main(x_721, x_703);
x_723 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_723, 0, x_722);
lean_inc(x_4);
lean_inc(x_2);
x_724 = l___private_Lean_Elab_App_2__elabArg(x_2, x_723, x_709, x_4, x_689);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
lean_inc(x_725);
x_727 = l_Lean_mkApp(x_2, x_725);
x_728 = lean_expr_instantiate1(x_95, x_725);
lean_dec(x_725);
lean_dec(x_95);
x_1 = x_605;
x_2 = x_727;
x_3 = x_728;
x_5 = x_726;
goto _start;
}
else
{
uint8_t x_730; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_730 = !lean_is_exclusive(x_724);
if (x_730 == 0)
{
return x_724;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_731 = lean_ctor_get(x_724, 0);
x_732 = lean_ctor_get(x_724, 1);
lean_inc(x_732);
lean_inc(x_731);
lean_dec(x_724);
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_731);
lean_ctor_set(x_733, 1, x_732);
return x_733;
}
}
}
}
}
else
{
lean_object* x_734; lean_object* x_735; 
lean_dec(x_675);
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_734 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_735 = l_Lean_Elab_Term_throwError___rarg(x_734, x_4, x_617);
return x_735;
}
}
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_736 = lean_ctor_get(x_672, 0);
lean_inc(x_736);
lean_dec(x_672);
lean_inc(x_736);
x_737 = l_Lean_mkApp(x_2, x_736);
x_738 = lean_expr_instantiate1(x_95, x_736);
lean_dec(x_736);
lean_dec(x_95);
x_1 = x_605;
x_2 = x_737;
x_3 = x_738;
x_5 = x_617;
goto _start;
}
}
else
{
lean_object* x_740; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_740 = lean_box(0);
x_618 = x_740;
goto block_671;
}
}
else
{
lean_object* x_741; lean_object* x_742; 
lean_dec(x_605);
lean_dec(x_93);
lean_dec(x_3);
x_741 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_742 = l___private_Lean_Elab_App_2__elabArg(x_2, x_741, x_94, x_4, x_617);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
lean_dec(x_742);
x_745 = lean_unsigned_to_nat(1u);
x_746 = lean_nat_add(x_10, x_745);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_746);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_604);
lean_inc(x_743);
x_747 = l_Lean_mkApp(x_2, x_743);
x_748 = lean_expr_instantiate1(x_95, x_743);
lean_dec(x_743);
lean_dec(x_95);
x_2 = x_747;
x_3 = x_748;
x_5 = x_744;
goto _start;
}
else
{
uint8_t x_750; 
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
x_750 = !lean_is_exclusive(x_742);
if (x_750 == 0)
{
return x_742;
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_742, 0);
x_752 = lean_ctor_get(x_742, 1);
lean_inc(x_752);
lean_inc(x_751);
lean_dec(x_742);
x_753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_753, 0, x_751);
lean_ctor_set(x_753, 1, x_752);
return x_753;
}
}
}
block_671:
{
uint8_t x_619; 
lean_dec(x_618);
x_619 = l_Array_isEmpty___rarg(x_11);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_620 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_620, 0, x_93);
x_621 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_622 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_620);
x_623 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_624 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
x_625 = x_11;
x_626 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_625);
x_627 = x_626;
x_628 = l_Array_toList___rarg(x_627);
lean_dec(x_627);
x_629 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_628);
x_630 = l_Array_HasRepr___rarg___closed__1;
x_631 = lean_string_append(x_630, x_629);
lean_dec(x_629);
x_632 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_632, 0, x_631);
x_633 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_633, 0, x_632);
x_634 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_634, 0, x_624);
lean_ctor_set(x_634, 1, x_633);
x_635 = l_Lean_Elab_Term_throwError___rarg(x_634, x_4, x_617);
return x_635;
}
else
{
lean_object* x_636; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; 
lean_dec(x_93);
lean_dec(x_11);
x_663 = l_Lean_Elab_Term_getOptions(x_4, x_617);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec(x_663);
x_666 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_667 = l_Lean_checkTraceOption(x_664, x_666);
lean_dec(x_664);
if (x_667 == 0)
{
x_636 = x_665;
goto block_662;
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_inc(x_2);
x_668 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_668, 0, x_2);
x_669 = l_Lean_Elab_Term_logTrace(x_666, x_668, x_4, x_665);
x_670 = lean_ctor_get(x_669, 1);
lean_inc(x_670);
lean_dec(x_669);
x_636 = x_670;
goto block_662;
}
block_662:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_637; 
lean_dec(x_3);
x_637 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_636);
lean_dec(x_12);
if (lean_obj_tag(x_637) == 0)
{
uint8_t x_638; 
x_638 = !lean_is_exclusive(x_637);
if (x_638 == 0)
{
lean_object* x_639; 
x_639 = lean_ctor_get(x_637, 0);
lean_dec(x_639);
lean_ctor_set(x_637, 0, x_2);
return x_637;
}
else
{
lean_object* x_640; lean_object* x_641; 
x_640 = lean_ctor_get(x_637, 1);
lean_inc(x_640);
lean_dec(x_637);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_2);
lean_ctor_set(x_641, 1, x_640);
return x_641;
}
}
else
{
uint8_t x_642; 
lean_dec(x_2);
x_642 = !lean_is_exclusive(x_637);
if (x_642 == 0)
{
return x_637;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_637, 0);
x_644 = lean_ctor_get(x_637, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_637);
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_643);
lean_ctor_set(x_645, 1, x_644);
return x_645;
}
}
}
else
{
lean_object* x_646; lean_object* x_647; 
x_646 = lean_ctor_get(x_8, 0);
lean_inc(x_646);
lean_dec(x_8);
lean_inc(x_4);
x_647 = l_Lean_Elab_Term_isDefEq(x_646, x_3, x_4, x_636);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; 
x_648 = lean_ctor_get(x_647, 1);
lean_inc(x_648);
lean_dec(x_647);
x_649 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_648);
lean_dec(x_12);
if (lean_obj_tag(x_649) == 0)
{
uint8_t x_650; 
x_650 = !lean_is_exclusive(x_649);
if (x_650 == 0)
{
lean_object* x_651; 
x_651 = lean_ctor_get(x_649, 0);
lean_dec(x_651);
lean_ctor_set(x_649, 0, x_2);
return x_649;
}
else
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_ctor_get(x_649, 1);
lean_inc(x_652);
lean_dec(x_649);
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_2);
lean_ctor_set(x_653, 1, x_652);
return x_653;
}
}
else
{
uint8_t x_654; 
lean_dec(x_2);
x_654 = !lean_is_exclusive(x_649);
if (x_654 == 0)
{
return x_649;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_649, 0);
x_656 = lean_ctor_get(x_649, 1);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_649);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_656);
return x_657;
}
}
}
else
{
uint8_t x_658; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_658 = !lean_is_exclusive(x_647);
if (x_658 == 0)
{
return x_647;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_647, 0);
x_660 = lean_ctor_get(x_647, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_647);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
return x_661;
}
}
}
}
}
}
}
else
{
uint8_t x_754; 
lean_free_object(x_1);
lean_dec(x_605);
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
x_754 = !lean_is_exclusive(x_608);
if (x_754 == 0)
{
return x_608;
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_755 = lean_ctor_get(x_608, 0);
x_756 = lean_ctor_get(x_608, 1);
lean_inc(x_756);
lean_inc(x_755);
lean_dec(x_608);
x_757 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_756);
return x_757;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_758; lean_object* x_759; 
x_758 = lean_ctor_get(x_608, 1);
lean_inc(x_758);
lean_dec(x_608);
if (x_607 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_811; 
x_811 = l_Lean_Expr_getOptParamDefault_x3f(x_94);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; 
x_812 = l_Lean_Expr_getAutoParamTactic_x3f(x_94);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_813 = lean_box(0);
x_759 = x_813;
goto block_810;
}
else
{
lean_object* x_814; 
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_814 = lean_ctor_get(x_812, 0);
lean_inc(x_814);
lean_dec(x_812);
if (lean_obj_tag(x_814) == 4)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_814, 0);
lean_inc(x_815);
lean_dec(x_814);
x_816 = l_Lean_Elab_Term_getEnv___rarg(x_758);
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec(x_816);
x_819 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_817, x_815);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
lean_dec(x_819);
x_821 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_821, 0, x_820);
x_822 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_822, 0, x_821);
x_823 = l_Lean_Elab_Term_throwError___rarg(x_822, x_4, x_818);
return x_823;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_824 = lean_ctor_get(x_819, 0);
lean_inc(x_824);
lean_dec(x_819);
x_825 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_818);
x_826 = lean_ctor_get(x_825, 1);
lean_inc(x_826);
lean_dec(x_825);
x_827 = l_Lean_Elab_Term_getMainModule___rarg(x_826);
x_828 = lean_ctor_get(x_827, 1);
lean_inc(x_828);
lean_dec(x_827);
x_829 = l_Lean_Syntax_getArgs(x_824);
lean_dec(x_824);
x_830 = l_Array_empty___closed__1;
x_831 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_829, x_829, x_97, x_830);
lean_dec(x_829);
x_832 = l_Lean_nullKind___closed__2;
x_833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_831);
x_834 = lean_array_push(x_830, x_833);
x_835 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_836 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_836, 0, x_835);
lean_ctor_set(x_836, 1, x_834);
x_837 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_838 = lean_array_push(x_837, x_836);
x_839 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_840 = lean_array_push(x_838, x_839);
x_841 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_842, 0, x_841);
lean_ctor_set(x_842, 1, x_840);
x_843 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_844 = l_Lean_Expr_getAppNumArgsAux___main(x_94, x_97);
x_845 = lean_nat_sub(x_844, x_97);
lean_dec(x_844);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_nat_sub(x_845, x_846);
lean_dec(x_845);
x_848 = l_Lean_Expr_getRevArg_x21___main(x_94, x_847);
lean_dec(x_94);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_849; lean_object* x_850; 
x_849 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_849, 0, x_842);
lean_inc(x_4);
lean_inc(x_2);
x_850 = l___private_Lean_Elab_App_2__elabArg(x_2, x_849, x_848, x_4, x_828);
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_851 = lean_ctor_get(x_850, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_850, 1);
lean_inc(x_852);
lean_dec(x_850);
lean_inc(x_851);
x_853 = l_Lean_mkApp(x_2, x_851);
x_854 = lean_expr_instantiate1(x_95, x_851);
lean_dec(x_851);
lean_dec(x_95);
x_1 = x_605;
x_2 = x_853;
x_3 = x_854;
x_5 = x_852;
goto _start;
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_856 = lean_ctor_get(x_850, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_850, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_850)) {
 lean_ctor_release(x_850, 0);
 lean_ctor_release(x_850, 1);
 x_858 = x_850;
} else {
 lean_dec_ref(x_850);
 x_858 = lean_box(0);
}
if (lean_is_scalar(x_858)) {
 x_859 = lean_alloc_ctor(1, 2, 0);
} else {
 x_859 = x_858;
}
lean_ctor_set(x_859, 0, x_856);
lean_ctor_set(x_859, 1, x_857);
return x_859;
}
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_860 = lean_ctor_get(x_843, 0);
lean_inc(x_860);
lean_dec(x_843);
x_861 = l_Lean_Syntax_replaceInfo___main(x_860, x_842);
x_862 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_862, 0, x_861);
lean_inc(x_4);
lean_inc(x_2);
x_863 = l___private_Lean_Elab_App_2__elabArg(x_2, x_862, x_848, x_4, x_828);
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_863, 1);
lean_inc(x_865);
lean_dec(x_863);
lean_inc(x_864);
x_866 = l_Lean_mkApp(x_2, x_864);
x_867 = lean_expr_instantiate1(x_95, x_864);
lean_dec(x_864);
lean_dec(x_95);
x_1 = x_605;
x_2 = x_866;
x_3 = x_867;
x_5 = x_865;
goto _start;
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_869 = lean_ctor_get(x_863, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_863, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 x_871 = x_863;
} else {
 lean_dec_ref(x_863);
 x_871 = lean_box(0);
}
if (lean_is_scalar(x_871)) {
 x_872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_872 = x_871;
}
lean_ctor_set(x_872, 0, x_869);
lean_ctor_set(x_872, 1, x_870);
return x_872;
}
}
}
}
else
{
lean_object* x_873; lean_object* x_874; 
lean_dec(x_814);
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_873 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_874 = l_Lean_Elab_Term_throwError___rarg(x_873, x_4, x_758);
return x_874;
}
}
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_875 = lean_ctor_get(x_811, 0);
lean_inc(x_875);
lean_dec(x_811);
lean_inc(x_875);
x_876 = l_Lean_mkApp(x_2, x_875);
x_877 = lean_expr_instantiate1(x_95, x_875);
lean_dec(x_875);
lean_dec(x_95);
x_1 = x_605;
x_2 = x_876;
x_3 = x_877;
x_5 = x_758;
goto _start;
}
}
else
{
lean_object* x_879; 
lean_dec(x_605);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_879 = lean_box(0);
x_759 = x_879;
goto block_810;
}
}
else
{
lean_object* x_880; lean_object* x_881; 
lean_dec(x_605);
lean_dec(x_93);
lean_dec(x_3);
x_880 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_881 = l___private_Lean_Elab_App_2__elabArg(x_2, x_880, x_94, x_4, x_758);
if (lean_obj_tag(x_881) == 0)
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec(x_881);
x_884 = lean_unsigned_to_nat(1u);
x_885 = lean_nat_add(x_10, x_884);
lean_dec(x_10);
x_886 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_886, 0, x_6);
lean_ctor_set(x_886, 1, x_7);
lean_ctor_set(x_886, 2, x_8);
lean_ctor_set(x_886, 3, x_885);
lean_ctor_set(x_886, 4, x_11);
lean_ctor_set(x_886, 5, x_12);
lean_ctor_set(x_886, 6, x_13);
lean_ctor_set_uint8(x_886, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_886, sizeof(void*)*7 + 1, x_604);
lean_inc(x_882);
x_887 = l_Lean_mkApp(x_2, x_882);
x_888 = lean_expr_instantiate1(x_95, x_882);
lean_dec(x_882);
lean_dec(x_95);
x_1 = x_886;
x_2 = x_887;
x_3 = x_888;
x_5 = x_883;
goto _start;
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
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
x_890 = lean_ctor_get(x_881, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_881, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_881)) {
 lean_ctor_release(x_881, 0);
 lean_ctor_release(x_881, 1);
 x_892 = x_881;
} else {
 lean_dec_ref(x_881);
 x_892 = lean_box(0);
}
if (lean_is_scalar(x_892)) {
 x_893 = lean_alloc_ctor(1, 2, 0);
} else {
 x_893 = x_892;
}
lean_ctor_set(x_893, 0, x_890);
lean_ctor_set(x_893, 1, x_891);
return x_893;
}
}
block_810:
{
uint8_t x_760; 
lean_dec(x_759);
x_760 = l_Array_isEmpty___rarg(x_11);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_761 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_761, 0, x_93);
x_762 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_763 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_761);
x_764 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_765 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set(x_765, 1, x_764);
x_766 = x_11;
x_767 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_766);
x_768 = x_767;
x_769 = l_Array_toList___rarg(x_768);
lean_dec(x_768);
x_770 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_769);
x_771 = l_Array_HasRepr___rarg___closed__1;
x_772 = lean_string_append(x_771, x_770);
lean_dec(x_770);
x_773 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_773, 0, x_772);
x_774 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_774, 0, x_773);
x_775 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_775, 0, x_765);
lean_ctor_set(x_775, 1, x_774);
x_776 = l_Lean_Elab_Term_throwError___rarg(x_775, x_4, x_758);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; uint8_t x_806; 
lean_dec(x_93);
lean_dec(x_11);
x_802 = l_Lean_Elab_Term_getOptions(x_4, x_758);
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
lean_dec(x_802);
x_805 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_806 = l_Lean_checkTraceOption(x_803, x_805);
lean_dec(x_803);
if (x_806 == 0)
{
x_777 = x_804;
goto block_801;
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; 
lean_inc(x_2);
x_807 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_807, 0, x_2);
x_808 = l_Lean_Elab_Term_logTrace(x_805, x_807, x_4, x_804);
x_809 = lean_ctor_get(x_808, 1);
lean_inc(x_809);
lean_dec(x_808);
x_777 = x_809;
goto block_801;
}
block_801:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_778; 
lean_dec(x_3);
x_778 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_777);
lean_dec(x_12);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_780 = x_778;
} else {
 lean_dec_ref(x_778);
 x_780 = lean_box(0);
}
if (lean_is_scalar(x_780)) {
 x_781 = lean_alloc_ctor(0, 2, 0);
} else {
 x_781 = x_780;
}
lean_ctor_set(x_781, 0, x_2);
lean_ctor_set(x_781, 1, x_779);
return x_781;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_dec(x_2);
x_782 = lean_ctor_get(x_778, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_778, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_784 = x_778;
} else {
 lean_dec_ref(x_778);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(1, 2, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_782);
lean_ctor_set(x_785, 1, x_783);
return x_785;
}
}
else
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_8, 0);
lean_inc(x_786);
lean_dec(x_8);
lean_inc(x_4);
x_787 = l_Lean_Elab_Term_isDefEq(x_786, x_3, x_4, x_777);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; 
x_788 = lean_ctor_get(x_787, 1);
lean_inc(x_788);
lean_dec(x_787);
x_789 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_788);
lean_dec(x_12);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_789, 1);
lean_inc(x_790);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_791 = x_789;
} else {
 lean_dec_ref(x_789);
 x_791 = lean_box(0);
}
if (lean_is_scalar(x_791)) {
 x_792 = lean_alloc_ctor(0, 2, 0);
} else {
 x_792 = x_791;
}
lean_ctor_set(x_792, 0, x_2);
lean_ctor_set(x_792, 1, x_790);
return x_792;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_2);
x_793 = lean_ctor_get(x_789, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_789, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_795 = x_789;
} else {
 lean_dec_ref(x_789);
 x_795 = lean_box(0);
}
if (lean_is_scalar(x_795)) {
 x_796 = lean_alloc_ctor(1, 2, 0);
} else {
 x_796 = x_795;
}
lean_ctor_set(x_796, 0, x_793);
lean_ctor_set(x_796, 1, x_794);
return x_796;
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_797 = lean_ctor_get(x_787, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_787, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_799 = x_787;
} else {
 lean_dec_ref(x_787);
 x_799 = lean_box(0);
}
if (lean_is_scalar(x_799)) {
 x_800 = lean_alloc_ctor(1, 2, 0);
} else {
 x_800 = x_799;
}
lean_ctor_set(x_800, 0, x_797);
lean_ctor_set(x_800, 1, x_798);
return x_800;
}
}
}
}
}
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
lean_dec(x_605);
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
x_894 = lean_ctor_get(x_608, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_608, 1);
lean_inc(x_895);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_896 = x_608;
} else {
 lean_dec_ref(x_608);
 x_896 = lean_box(0);
}
if (lean_is_scalar(x_896)) {
 x_897 = lean_alloc_ctor(1, 2, 0);
} else {
 x_897 = x_896;
}
lean_ctor_set(x_897, 0, x_894);
lean_ctor_set(x_897, 1, x_895);
return x_897;
}
}
}
case 3:
{
if (x_9 == 0)
{
uint8_t x_898; 
lean_dec(x_93);
lean_dec(x_19);
lean_dec(x_3);
x_898 = !lean_is_exclusive(x_1);
if (x_898 == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; uint8_t x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_899 = lean_ctor_get(x_1, 6);
lean_dec(x_899);
x_900 = lean_ctor_get(x_1, 5);
lean_dec(x_900);
x_901 = lean_ctor_get(x_1, 4);
lean_dec(x_901);
x_902 = lean_ctor_get(x_1, 3);
lean_dec(x_902);
x_903 = lean_ctor_get(x_1, 2);
lean_dec(x_903);
x_904 = lean_ctor_get(x_1, 1);
lean_dec(x_904);
x_905 = lean_ctor_get(x_1, 0);
lean_dec(x_905);
x_906 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_906, 0, x_94);
x_907 = 1;
x_908 = lean_box(0);
lean_inc(x_4);
x_909 = l_Lean_Elab_Term_mkFreshExprMVar(x_906, x_907, x_908, x_4, x_20);
x_910 = lean_ctor_get(x_909, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_909, 1);
lean_inc(x_911);
lean_dec(x_909);
x_912 = l_Lean_Expr_mvarId_x21(x_910);
x_913 = lean_array_push(x_12, x_912);
lean_ctor_set(x_1, 5, x_913);
lean_inc(x_910);
x_914 = l_Lean_mkApp(x_2, x_910);
x_915 = lean_expr_instantiate1(x_95, x_910);
lean_dec(x_910);
lean_dec(x_95);
x_2 = x_914;
x_3 = x_915;
x_5 = x_911;
goto _start;
}
else
{
lean_object* x_917; uint8_t x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
lean_dec(x_1);
x_917 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_917, 0, x_94);
x_918 = 1;
x_919 = lean_box(0);
lean_inc(x_4);
x_920 = l_Lean_Elab_Term_mkFreshExprMVar(x_917, x_918, x_919, x_4, x_20);
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
lean_dec(x_920);
x_923 = l_Lean_Expr_mvarId_x21(x_921);
x_924 = lean_array_push(x_12, x_923);
x_925 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_925, 0, x_6);
lean_ctor_set(x_925, 1, x_7);
lean_ctor_set(x_925, 2, x_8);
lean_ctor_set(x_925, 3, x_10);
lean_ctor_set(x_925, 4, x_11);
lean_ctor_set(x_925, 5, x_924);
lean_ctor_set(x_925, 6, x_13);
lean_ctor_set_uint8(x_925, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_925, sizeof(void*)*7 + 1, x_15);
lean_inc(x_921);
x_926 = l_Lean_mkApp(x_2, x_921);
x_927 = lean_expr_instantiate1(x_95, x_921);
lean_dec(x_921);
lean_dec(x_95);
x_1 = x_925;
x_2 = x_926;
x_3 = x_927;
x_5 = x_922;
goto _start;
}
}
else
{
uint8_t x_929; 
x_929 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_929 == 0)
{
lean_object* x_930; uint8_t x_931; lean_object* x_932; uint8_t x_933; 
x_930 = lean_array_get_size(x_7);
x_931 = lean_nat_dec_lt(x_10, x_930);
lean_dec(x_930);
lean_inc(x_4);
lean_inc(x_1);
x_932 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_19, x_4, x_20);
x_933 = !lean_is_exclusive(x_1);
if (x_933 == 0)
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_934 = lean_ctor_get(x_1, 6);
lean_dec(x_934);
x_935 = lean_ctor_get(x_1, 5);
lean_dec(x_935);
x_936 = lean_ctor_get(x_1, 4);
lean_dec(x_936);
x_937 = lean_ctor_get(x_1, 3);
lean_dec(x_937);
x_938 = lean_ctor_get(x_1, 2);
lean_dec(x_938);
x_939 = lean_ctor_get(x_1, 1);
lean_dec(x_939);
x_940 = lean_ctor_get(x_1, 0);
lean_dec(x_940);
if (lean_obj_tag(x_932) == 0)
{
if (x_931 == 0)
{
lean_object* x_941; uint8_t x_942; 
lean_free_object(x_1);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_941 = lean_ctor_get(x_932, 1);
lean_inc(x_941);
lean_dec(x_932);
x_942 = l_Array_isEmpty___rarg(x_11);
if (x_942 == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_943 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_943, 0, x_93);
x_944 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_945 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_945, 0, x_944);
lean_ctor_set(x_945, 1, x_943);
x_946 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_947 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_947, 0, x_945);
lean_ctor_set(x_947, 1, x_946);
x_948 = x_11;
x_949 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_948);
x_950 = x_949;
x_951 = l_Array_toList___rarg(x_950);
lean_dec(x_950);
x_952 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_951);
x_953 = l_Array_HasRepr___rarg___closed__1;
x_954 = lean_string_append(x_953, x_952);
lean_dec(x_952);
x_955 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_955, 0, x_954);
x_956 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_956, 0, x_955);
x_957 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_957, 0, x_947);
lean_ctor_set(x_957, 1, x_956);
x_958 = l_Lean_Elab_Term_throwError___rarg(x_957, x_4, x_941);
return x_958;
}
else
{
lean_object* x_959; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; uint8_t x_990; 
lean_dec(x_93);
lean_dec(x_11);
x_986 = l_Lean_Elab_Term_getOptions(x_4, x_941);
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_986, 1);
lean_inc(x_988);
lean_dec(x_986);
x_989 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_990 = l_Lean_checkTraceOption(x_987, x_989);
lean_dec(x_987);
if (x_990 == 0)
{
x_959 = x_988;
goto block_985;
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_inc(x_2);
x_991 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_991, 0, x_2);
x_992 = l_Lean_Elab_Term_logTrace(x_989, x_991, x_4, x_988);
x_993 = lean_ctor_get(x_992, 1);
lean_inc(x_993);
lean_dec(x_992);
x_959 = x_993;
goto block_985;
}
block_985:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_960; 
lean_dec(x_3);
x_960 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_959);
lean_dec(x_12);
if (lean_obj_tag(x_960) == 0)
{
uint8_t x_961; 
x_961 = !lean_is_exclusive(x_960);
if (x_961 == 0)
{
lean_object* x_962; 
x_962 = lean_ctor_get(x_960, 0);
lean_dec(x_962);
lean_ctor_set(x_960, 0, x_2);
return x_960;
}
else
{
lean_object* x_963; lean_object* x_964; 
x_963 = lean_ctor_get(x_960, 1);
lean_inc(x_963);
lean_dec(x_960);
x_964 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_964, 0, x_2);
lean_ctor_set(x_964, 1, x_963);
return x_964;
}
}
else
{
uint8_t x_965; 
lean_dec(x_2);
x_965 = !lean_is_exclusive(x_960);
if (x_965 == 0)
{
return x_960;
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_966 = lean_ctor_get(x_960, 0);
x_967 = lean_ctor_get(x_960, 1);
lean_inc(x_967);
lean_inc(x_966);
lean_dec(x_960);
x_968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_968, 0, x_966);
lean_ctor_set(x_968, 1, x_967);
return x_968;
}
}
}
else
{
lean_object* x_969; lean_object* x_970; 
x_969 = lean_ctor_get(x_8, 0);
lean_inc(x_969);
lean_dec(x_8);
lean_inc(x_4);
x_970 = l_Lean_Elab_Term_isDefEq(x_969, x_3, x_4, x_959);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; 
x_971 = lean_ctor_get(x_970, 1);
lean_inc(x_971);
lean_dec(x_970);
x_972 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_971);
lean_dec(x_12);
if (lean_obj_tag(x_972) == 0)
{
uint8_t x_973; 
x_973 = !lean_is_exclusive(x_972);
if (x_973 == 0)
{
lean_object* x_974; 
x_974 = lean_ctor_get(x_972, 0);
lean_dec(x_974);
lean_ctor_set(x_972, 0, x_2);
return x_972;
}
else
{
lean_object* x_975; lean_object* x_976; 
x_975 = lean_ctor_get(x_972, 1);
lean_inc(x_975);
lean_dec(x_972);
x_976 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_976, 0, x_2);
lean_ctor_set(x_976, 1, x_975);
return x_976;
}
}
else
{
uint8_t x_977; 
lean_dec(x_2);
x_977 = !lean_is_exclusive(x_972);
if (x_977 == 0)
{
return x_972;
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_978 = lean_ctor_get(x_972, 0);
x_979 = lean_ctor_get(x_972, 1);
lean_inc(x_979);
lean_inc(x_978);
lean_dec(x_972);
x_980 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_980, 0, x_978);
lean_ctor_set(x_980, 1, x_979);
return x_980;
}
}
}
else
{
uint8_t x_981; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_981 = !lean_is_exclusive(x_970);
if (x_981 == 0)
{
return x_970;
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_982 = lean_ctor_get(x_970, 0);
x_983 = lean_ctor_get(x_970, 1);
lean_inc(x_983);
lean_inc(x_982);
lean_dec(x_970);
x_984 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_984, 0, x_982);
lean_ctor_set(x_984, 1, x_983);
return x_984;
}
}
}
}
}
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; 
lean_dec(x_93);
lean_dec(x_3);
x_994 = lean_ctor_get(x_932, 1);
lean_inc(x_994);
lean_dec(x_932);
x_995 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_996 = l___private_Lean_Elab_App_2__elabArg(x_2, x_995, x_94, x_4, x_994);
if (lean_obj_tag(x_996) == 0)
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; uint8_t x_1001; lean_object* x_1002; lean_object* x_1003; 
x_997 = lean_ctor_get(x_996, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_996, 1);
lean_inc(x_998);
lean_dec(x_996);
x_999 = lean_unsigned_to_nat(1u);
x_1000 = lean_nat_add(x_10, x_999);
lean_dec(x_10);
x_1001 = 1;
lean_ctor_set(x_1, 3, x_1000);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_1001);
lean_inc(x_997);
x_1002 = l_Lean_mkApp(x_2, x_997);
x_1003 = lean_expr_instantiate1(x_95, x_997);
lean_dec(x_997);
lean_dec(x_95);
x_2 = x_1002;
x_3 = x_1003;
x_5 = x_998;
goto _start;
}
else
{
uint8_t x_1005; 
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
x_1005 = !lean_is_exclusive(x_996);
if (x_1005 == 0)
{
return x_996;
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1006 = lean_ctor_get(x_996, 0);
x_1007 = lean_ctor_get(x_996, 1);
lean_inc(x_1007);
lean_inc(x_1006);
lean_dec(x_996);
x_1008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1008, 0, x_1006);
lean_ctor_set(x_1008, 1, x_1007);
return x_1008;
}
}
}
}
else
{
uint8_t x_1009; 
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
x_1009 = !lean_is_exclusive(x_932);
if (x_1009 == 0)
{
return x_932;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_932, 0);
x_1011 = lean_ctor_get(x_932, 1);
lean_inc(x_1011);
lean_inc(x_1010);
lean_dec(x_932);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
return x_1012;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_932) == 0)
{
if (x_931 == 0)
{
lean_object* x_1013; uint8_t x_1014; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_1013 = lean_ctor_get(x_932, 1);
lean_inc(x_1013);
lean_dec(x_932);
x_1014 = l_Array_isEmpty___rarg(x_11);
if (x_1014 == 0)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1015 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1015, 0, x_93);
x_1016 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1017 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_1015);
x_1018 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1019 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1019, 0, x_1017);
lean_ctor_set(x_1019, 1, x_1018);
x_1020 = x_11;
x_1021 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_1020);
x_1022 = x_1021;
x_1023 = l_Array_toList___rarg(x_1022);
lean_dec(x_1022);
x_1024 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1023);
x_1025 = l_Array_HasRepr___rarg___closed__1;
x_1026 = lean_string_append(x_1025, x_1024);
lean_dec(x_1024);
x_1027 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1027, 0, x_1026);
x_1028 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1028, 0, x_1027);
x_1029 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1029, 0, x_1019);
lean_ctor_set(x_1029, 1, x_1028);
x_1030 = l_Lean_Elab_Term_throwError___rarg(x_1029, x_4, x_1013);
return x_1030;
}
else
{
lean_object* x_1031; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; uint8_t x_1060; 
lean_dec(x_93);
lean_dec(x_11);
x_1056 = l_Lean_Elab_Term_getOptions(x_4, x_1013);
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1056, 1);
lean_inc(x_1058);
lean_dec(x_1056);
x_1059 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1060 = l_Lean_checkTraceOption(x_1057, x_1059);
lean_dec(x_1057);
if (x_1060 == 0)
{
x_1031 = x_1058;
goto block_1055;
}
else
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
lean_inc(x_2);
x_1061 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1061, 0, x_2);
x_1062 = l_Lean_Elab_Term_logTrace(x_1059, x_1061, x_4, x_1058);
x_1063 = lean_ctor_get(x_1062, 1);
lean_inc(x_1063);
lean_dec(x_1062);
x_1031 = x_1063;
goto block_1055;
}
block_1055:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1032; 
lean_dec(x_3);
x_1032 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_1031);
lean_dec(x_12);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1033 = lean_ctor_get(x_1032, 1);
lean_inc(x_1033);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 lean_ctor_release(x_1032, 1);
 x_1034 = x_1032;
} else {
 lean_dec_ref(x_1032);
 x_1034 = lean_box(0);
}
if (lean_is_scalar(x_1034)) {
 x_1035 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1035 = x_1034;
}
lean_ctor_set(x_1035, 0, x_2);
lean_ctor_set(x_1035, 1, x_1033);
return x_1035;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
lean_dec(x_2);
x_1036 = lean_ctor_get(x_1032, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_1032, 1);
lean_inc(x_1037);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 lean_ctor_release(x_1032, 1);
 x_1038 = x_1032;
} else {
 lean_dec_ref(x_1032);
 x_1038 = lean_box(0);
}
if (lean_is_scalar(x_1038)) {
 x_1039 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1039 = x_1038;
}
lean_ctor_set(x_1039, 0, x_1036);
lean_ctor_set(x_1039, 1, x_1037);
return x_1039;
}
}
else
{
lean_object* x_1040; lean_object* x_1041; 
x_1040 = lean_ctor_get(x_8, 0);
lean_inc(x_1040);
lean_dec(x_8);
lean_inc(x_4);
x_1041 = l_Lean_Elab_Term_isDefEq(x_1040, x_3, x_4, x_1031);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; lean_object* x_1043; 
x_1042 = lean_ctor_get(x_1041, 1);
lean_inc(x_1042);
lean_dec(x_1041);
x_1043 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_1042);
lean_dec(x_12);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
x_1044 = lean_ctor_get(x_1043, 1);
lean_inc(x_1044);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1045 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1045 = lean_box(0);
}
if (lean_is_scalar(x_1045)) {
 x_1046 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1046 = x_1045;
}
lean_ctor_set(x_1046, 0, x_2);
lean_ctor_set(x_1046, 1, x_1044);
return x_1046;
}
else
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
lean_dec(x_2);
x_1047 = lean_ctor_get(x_1043, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1043, 1);
lean_inc(x_1048);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1049 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1049 = lean_box(0);
}
if (lean_is_scalar(x_1049)) {
 x_1050 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1050 = x_1049;
}
lean_ctor_set(x_1050, 0, x_1047);
lean_ctor_set(x_1050, 1, x_1048);
return x_1050;
}
}
else
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_1051 = lean_ctor_get(x_1041, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1041, 1);
lean_inc(x_1052);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1053 = x_1041;
} else {
 lean_dec_ref(x_1041);
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
}
}
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
lean_dec(x_93);
lean_dec(x_3);
x_1064 = lean_ctor_get(x_932, 1);
lean_inc(x_1064);
lean_dec(x_932);
x_1065 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_1066 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1065, x_94, x_4, x_1064);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; uint8_t x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1067 = lean_ctor_get(x_1066, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1066, 1);
lean_inc(x_1068);
lean_dec(x_1066);
x_1069 = lean_unsigned_to_nat(1u);
x_1070 = lean_nat_add(x_10, x_1069);
lean_dec(x_10);
x_1071 = 1;
x_1072 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1072, 0, x_6);
lean_ctor_set(x_1072, 1, x_7);
lean_ctor_set(x_1072, 2, x_8);
lean_ctor_set(x_1072, 3, x_1070);
lean_ctor_set(x_1072, 4, x_11);
lean_ctor_set(x_1072, 5, x_12);
lean_ctor_set(x_1072, 6, x_13);
lean_ctor_set_uint8(x_1072, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1072, sizeof(void*)*7 + 1, x_1071);
lean_inc(x_1067);
x_1073 = l_Lean_mkApp(x_2, x_1067);
x_1074 = lean_expr_instantiate1(x_95, x_1067);
lean_dec(x_1067);
lean_dec(x_95);
x_1 = x_1072;
x_2 = x_1073;
x_3 = x_1074;
x_5 = x_1068;
goto _start;
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
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
x_1076 = lean_ctor_get(x_1066, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1066, 1);
lean_inc(x_1077);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1078 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1078 = lean_box(0);
}
if (lean_is_scalar(x_1078)) {
 x_1079 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1079 = x_1078;
}
lean_ctor_set(x_1079, 0, x_1076);
lean_ctor_set(x_1079, 1, x_1077);
return x_1079;
}
}
}
else
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
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
x_1080 = lean_ctor_get(x_932, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_932, 1);
lean_inc(x_1081);
if (lean_is_exclusive(x_932)) {
 lean_ctor_release(x_932, 0);
 lean_ctor_release(x_932, 1);
 x_1082 = x_932;
} else {
 lean_dec_ref(x_932);
 x_1082 = lean_box(0);
}
if (lean_is_scalar(x_1082)) {
 x_1083 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1083 = x_1082;
}
lean_ctor_set(x_1083, 0, x_1080);
lean_ctor_set(x_1083, 1, x_1081);
return x_1083;
}
}
}
else
{
uint8_t x_1084; 
lean_dec(x_93);
lean_dec(x_19);
lean_dec(x_3);
x_1084 = !lean_is_exclusive(x_1);
if (x_1084 == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; uint8_t x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
x_1085 = lean_ctor_get(x_1, 6);
lean_dec(x_1085);
x_1086 = lean_ctor_get(x_1, 5);
lean_dec(x_1086);
x_1087 = lean_ctor_get(x_1, 4);
lean_dec(x_1087);
x_1088 = lean_ctor_get(x_1, 3);
lean_dec(x_1088);
x_1089 = lean_ctor_get(x_1, 2);
lean_dec(x_1089);
x_1090 = lean_ctor_get(x_1, 1);
lean_dec(x_1090);
x_1091 = lean_ctor_get(x_1, 0);
lean_dec(x_1091);
x_1092 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1092, 0, x_94);
x_1093 = 1;
x_1094 = lean_box(0);
lean_inc(x_4);
x_1095 = l_Lean_Elab_Term_mkFreshExprMVar(x_1092, x_1093, x_1094, x_4, x_20);
x_1096 = lean_ctor_get(x_1095, 0);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1095, 1);
lean_inc(x_1097);
lean_dec(x_1095);
x_1098 = lean_unsigned_to_nat(1u);
x_1099 = lean_nat_add(x_10, x_1098);
lean_dec(x_10);
x_1100 = l_Lean_Expr_mvarId_x21(x_1096);
x_1101 = lean_array_push(x_12, x_1100);
lean_ctor_set(x_1, 5, x_1101);
lean_ctor_set(x_1, 3, x_1099);
lean_inc(x_1096);
x_1102 = l_Lean_mkApp(x_2, x_1096);
x_1103 = lean_expr_instantiate1(x_95, x_1096);
lean_dec(x_1096);
lean_dec(x_95);
x_2 = x_1102;
x_3 = x_1103;
x_5 = x_1097;
goto _start;
}
else
{
lean_object* x_1105; uint8_t x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
lean_dec(x_1);
x_1105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1105, 0, x_94);
x_1106 = 1;
x_1107 = lean_box(0);
lean_inc(x_4);
x_1108 = l_Lean_Elab_Term_mkFreshExprMVar(x_1105, x_1106, x_1107, x_4, x_20);
x_1109 = lean_ctor_get(x_1108, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1108, 1);
lean_inc(x_1110);
lean_dec(x_1108);
x_1111 = lean_unsigned_to_nat(1u);
x_1112 = lean_nat_add(x_10, x_1111);
lean_dec(x_10);
x_1113 = l_Lean_Expr_mvarId_x21(x_1109);
x_1114 = lean_array_push(x_12, x_1113);
x_1115 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1115, 0, x_6);
lean_ctor_set(x_1115, 1, x_7);
lean_ctor_set(x_1115, 2, x_8);
lean_ctor_set(x_1115, 3, x_1112);
lean_ctor_set(x_1115, 4, x_11);
lean_ctor_set(x_1115, 5, x_1114);
lean_ctor_set(x_1115, 6, x_13);
lean_ctor_set_uint8(x_1115, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1115, sizeof(void*)*7 + 1, x_15);
lean_inc(x_1109);
x_1116 = l_Lean_mkApp(x_2, x_1109);
x_1117 = lean_expr_instantiate1(x_95, x_1109);
lean_dec(x_1109);
lean_dec(x_95);
x_1 = x_1115;
x_2 = x_1116;
x_3 = x_1117;
x_5 = x_1110;
goto _start;
}
}
}
}
default: 
{
uint8_t x_1119; lean_object* x_1120; lean_object* x_1121; uint8_t x_1122; lean_object* x_1123; uint8_t x_1124; 
x_1119 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1120 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1120, 0, x_6);
lean_ctor_set(x_1120, 1, x_7);
lean_ctor_set(x_1120, 2, x_8);
lean_ctor_set(x_1120, 3, x_10);
lean_ctor_set(x_1120, 4, x_11);
lean_ctor_set(x_1120, 5, x_12);
lean_ctor_set(x_1120, 6, x_13);
lean_ctor_set_uint8(x_1120, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1120, sizeof(void*)*7 + 1, x_1119);
x_1121 = lean_array_get_size(x_7);
x_1122 = lean_nat_dec_lt(x_10, x_1121);
lean_dec(x_1121);
lean_inc(x_4);
lean_inc(x_1);
x_1123 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_19, x_4, x_20);
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
lean_object* x_1132; lean_object* x_1133; 
x_1132 = lean_ctor_get(x_1123, 1);
lean_inc(x_1132);
lean_dec(x_1123);
if (x_1122 == 0)
{
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1187; 
x_1187 = l_Lean_Expr_getOptParamDefault_x3f(x_94);
if (lean_obj_tag(x_1187) == 0)
{
lean_object* x_1188; 
x_1188 = l_Lean_Expr_getAutoParamTactic_x3f(x_94);
if (lean_obj_tag(x_1188) == 0)
{
lean_object* x_1189; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_1189 = lean_box(0);
x_1133 = x_1189;
goto block_1186;
}
else
{
lean_object* x_1190; 
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1190 = lean_ctor_get(x_1188, 0);
lean_inc(x_1190);
lean_dec(x_1188);
if (lean_obj_tag(x_1190) == 4)
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1191 = lean_ctor_get(x_1190, 0);
lean_inc(x_1191);
lean_dec(x_1190);
x_1192 = l_Lean_Elab_Term_getEnv___rarg(x_1132);
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
x_1194 = lean_ctor_get(x_1192, 1);
lean_inc(x_1194);
lean_dec(x_1192);
x_1195 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1193, x_1191);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
lean_dec(x_1195);
x_1197 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1197, 0, x_1196);
x_1198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1198, 0, x_1197);
x_1199 = l_Lean_Elab_Term_throwError___rarg(x_1198, x_4, x_1194);
return x_1199;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1200 = lean_ctor_get(x_1195, 0);
lean_inc(x_1200);
lean_dec(x_1195);
x_1201 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1194);
x_1202 = lean_ctor_get(x_1201, 1);
lean_inc(x_1202);
lean_dec(x_1201);
x_1203 = l_Lean_Elab_Term_getMainModule___rarg(x_1202);
x_1204 = lean_ctor_get(x_1203, 1);
lean_inc(x_1204);
lean_dec(x_1203);
x_1205 = l_Lean_Syntax_getArgs(x_1200);
lean_dec(x_1200);
x_1206 = l_Array_empty___closed__1;
x_1207 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1205, x_1205, x_97, x_1206);
lean_dec(x_1205);
x_1208 = l_Lean_nullKind___closed__2;
x_1209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1209, 0, x_1208);
lean_ctor_set(x_1209, 1, x_1207);
x_1210 = lean_array_push(x_1206, x_1209);
x_1211 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_1212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1212, 0, x_1211);
lean_ctor_set(x_1212, 1, x_1210);
x_1213 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1214 = lean_array_push(x_1213, x_1212);
x_1215 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1216 = lean_array_push(x_1214, x_1215);
x_1217 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1218, 0, x_1217);
lean_ctor_set(x_1218, 1, x_1216);
x_1219 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_1220 = l_Lean_Expr_getAppNumArgsAux___main(x_94, x_97);
x_1221 = lean_nat_sub(x_1220, x_97);
lean_dec(x_1220);
x_1222 = lean_unsigned_to_nat(1u);
x_1223 = lean_nat_sub(x_1221, x_1222);
lean_dec(x_1221);
x_1224 = l_Lean_Expr_getRevArg_x21___main(x_94, x_1223);
lean_dec(x_94);
if (lean_obj_tag(x_1219) == 0)
{
lean_object* x_1225; lean_object* x_1226; 
x_1225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1225, 0, x_1218);
lean_inc(x_4);
lean_inc(x_2);
x_1226 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1225, x_1224, x_4, x_1204);
if (lean_obj_tag(x_1226) == 0)
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; 
x_1227 = lean_ctor_get(x_1226, 0);
lean_inc(x_1227);
x_1228 = lean_ctor_get(x_1226, 1);
lean_inc(x_1228);
lean_dec(x_1226);
lean_inc(x_1227);
x_1229 = l_Lean_mkApp(x_2, x_1227);
x_1230 = lean_expr_instantiate1(x_95, x_1227);
lean_dec(x_1227);
lean_dec(x_95);
x_1 = x_1120;
x_2 = x_1229;
x_3 = x_1230;
x_5 = x_1228;
goto _start;
}
else
{
uint8_t x_1232; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_1232 = !lean_is_exclusive(x_1226);
if (x_1232 == 0)
{
return x_1226;
}
else
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1233 = lean_ctor_get(x_1226, 0);
x_1234 = lean_ctor_get(x_1226, 1);
lean_inc(x_1234);
lean_inc(x_1233);
lean_dec(x_1226);
x_1235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1235, 0, x_1233);
lean_ctor_set(x_1235, 1, x_1234);
return x_1235;
}
}
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
x_1236 = lean_ctor_get(x_1219, 0);
lean_inc(x_1236);
lean_dec(x_1219);
x_1237 = l_Lean_Syntax_replaceInfo___main(x_1236, x_1218);
x_1238 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1238, 0, x_1237);
lean_inc(x_4);
lean_inc(x_2);
x_1239 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1238, x_1224, x_4, x_1204);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1240 = lean_ctor_get(x_1239, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1239, 1);
lean_inc(x_1241);
lean_dec(x_1239);
lean_inc(x_1240);
x_1242 = l_Lean_mkApp(x_2, x_1240);
x_1243 = lean_expr_instantiate1(x_95, x_1240);
lean_dec(x_1240);
lean_dec(x_95);
x_1 = x_1120;
x_2 = x_1242;
x_3 = x_1243;
x_5 = x_1241;
goto _start;
}
else
{
uint8_t x_1245; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_1245 = !lean_is_exclusive(x_1239);
if (x_1245 == 0)
{
return x_1239;
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1246 = lean_ctor_get(x_1239, 0);
x_1247 = lean_ctor_get(x_1239, 1);
lean_inc(x_1247);
lean_inc(x_1246);
lean_dec(x_1239);
x_1248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1248, 0, x_1246);
lean_ctor_set(x_1248, 1, x_1247);
return x_1248;
}
}
}
}
}
else
{
lean_object* x_1249; lean_object* x_1250; 
lean_dec(x_1190);
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_1249 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1250 = l_Lean_Elab_Term_throwError___rarg(x_1249, x_4, x_1132);
return x_1250;
}
}
}
else
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1251 = lean_ctor_get(x_1187, 0);
lean_inc(x_1251);
lean_dec(x_1187);
lean_inc(x_1251);
x_1252 = l_Lean_mkApp(x_2, x_1251);
x_1253 = lean_expr_instantiate1(x_95, x_1251);
lean_dec(x_1251);
lean_dec(x_95);
x_1 = x_1120;
x_2 = x_1252;
x_3 = x_1253;
x_5 = x_1132;
goto _start;
}
}
else
{
lean_object* x_1255; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_1255 = lean_box(0);
x_1133 = x_1255;
goto block_1186;
}
}
else
{
lean_object* x_1256; lean_object* x_1257; 
lean_dec(x_1120);
lean_dec(x_93);
lean_dec(x_3);
x_1256 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_1257 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1256, x_94, x_4, x_1132);
if (lean_obj_tag(x_1257) == 0)
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
x_1258 = lean_ctor_get(x_1257, 0);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_1257, 1);
lean_inc(x_1259);
lean_dec(x_1257);
x_1260 = lean_unsigned_to_nat(1u);
x_1261 = lean_nat_add(x_10, x_1260);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_1261);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_1119);
lean_inc(x_1258);
x_1262 = l_Lean_mkApp(x_2, x_1258);
x_1263 = lean_expr_instantiate1(x_95, x_1258);
lean_dec(x_1258);
lean_dec(x_95);
x_2 = x_1262;
x_3 = x_1263;
x_5 = x_1259;
goto _start;
}
else
{
uint8_t x_1265; 
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
x_1265 = !lean_is_exclusive(x_1257);
if (x_1265 == 0)
{
return x_1257;
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
x_1266 = lean_ctor_get(x_1257, 0);
x_1267 = lean_ctor_get(x_1257, 1);
lean_inc(x_1267);
lean_inc(x_1266);
lean_dec(x_1257);
x_1268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1268, 0, x_1266);
lean_ctor_set(x_1268, 1, x_1267);
return x_1268;
}
}
}
block_1186:
{
uint8_t x_1134; 
lean_dec(x_1133);
x_1134 = l_Array_isEmpty___rarg(x_11);
if (x_1134 == 0)
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1135 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1135, 0, x_93);
x_1136 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1137, 0, x_1136);
lean_ctor_set(x_1137, 1, x_1135);
x_1138 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1139 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1139, 0, x_1137);
lean_ctor_set(x_1139, 1, x_1138);
x_1140 = x_11;
x_1141 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_1140);
x_1142 = x_1141;
x_1143 = l_Array_toList___rarg(x_1142);
lean_dec(x_1142);
x_1144 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1143);
x_1145 = l_Array_HasRepr___rarg___closed__1;
x_1146 = lean_string_append(x_1145, x_1144);
lean_dec(x_1144);
x_1147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1147, 0, x_1146);
x_1148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1148, 0, x_1147);
x_1149 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1149, 0, x_1139);
lean_ctor_set(x_1149, 1, x_1148);
x_1150 = l_Lean_Elab_Term_throwError___rarg(x_1149, x_4, x_1132);
return x_1150;
}
else
{
lean_object* x_1151; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; uint8_t x_1182; 
lean_dec(x_93);
lean_dec(x_11);
x_1178 = l_Lean_Elab_Term_getOptions(x_4, x_1132);
x_1179 = lean_ctor_get(x_1178, 0);
lean_inc(x_1179);
x_1180 = lean_ctor_get(x_1178, 1);
lean_inc(x_1180);
lean_dec(x_1178);
x_1181 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1182 = l_Lean_checkTraceOption(x_1179, x_1181);
lean_dec(x_1179);
if (x_1182 == 0)
{
x_1151 = x_1180;
goto block_1177;
}
else
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; 
lean_inc(x_2);
x_1183 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1183, 0, x_2);
x_1184 = l_Lean_Elab_Term_logTrace(x_1181, x_1183, x_4, x_1180);
x_1185 = lean_ctor_get(x_1184, 1);
lean_inc(x_1185);
lean_dec(x_1184);
x_1151 = x_1185;
goto block_1177;
}
block_1177:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1152; 
lean_dec(x_3);
x_1152 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_1151);
lean_dec(x_12);
if (lean_obj_tag(x_1152) == 0)
{
uint8_t x_1153; 
x_1153 = !lean_is_exclusive(x_1152);
if (x_1153 == 0)
{
lean_object* x_1154; 
x_1154 = lean_ctor_get(x_1152, 0);
lean_dec(x_1154);
lean_ctor_set(x_1152, 0, x_2);
return x_1152;
}
else
{
lean_object* x_1155; lean_object* x_1156; 
x_1155 = lean_ctor_get(x_1152, 1);
lean_inc(x_1155);
lean_dec(x_1152);
x_1156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1156, 0, x_2);
lean_ctor_set(x_1156, 1, x_1155);
return x_1156;
}
}
else
{
uint8_t x_1157; 
lean_dec(x_2);
x_1157 = !lean_is_exclusive(x_1152);
if (x_1157 == 0)
{
return x_1152;
}
else
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
x_1158 = lean_ctor_get(x_1152, 0);
x_1159 = lean_ctor_get(x_1152, 1);
lean_inc(x_1159);
lean_inc(x_1158);
lean_dec(x_1152);
x_1160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1160, 0, x_1158);
lean_ctor_set(x_1160, 1, x_1159);
return x_1160;
}
}
}
else
{
lean_object* x_1161; lean_object* x_1162; 
x_1161 = lean_ctor_get(x_8, 0);
lean_inc(x_1161);
lean_dec(x_8);
lean_inc(x_4);
x_1162 = l_Lean_Elab_Term_isDefEq(x_1161, x_3, x_4, x_1151);
if (lean_obj_tag(x_1162) == 0)
{
lean_object* x_1163; lean_object* x_1164; 
x_1163 = lean_ctor_get(x_1162, 1);
lean_inc(x_1163);
lean_dec(x_1162);
x_1164 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_1163);
lean_dec(x_12);
if (lean_obj_tag(x_1164) == 0)
{
uint8_t x_1165; 
x_1165 = !lean_is_exclusive(x_1164);
if (x_1165 == 0)
{
lean_object* x_1166; 
x_1166 = lean_ctor_get(x_1164, 0);
lean_dec(x_1166);
lean_ctor_set(x_1164, 0, x_2);
return x_1164;
}
else
{
lean_object* x_1167; lean_object* x_1168; 
x_1167 = lean_ctor_get(x_1164, 1);
lean_inc(x_1167);
lean_dec(x_1164);
x_1168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1168, 0, x_2);
lean_ctor_set(x_1168, 1, x_1167);
return x_1168;
}
}
else
{
uint8_t x_1169; 
lean_dec(x_2);
x_1169 = !lean_is_exclusive(x_1164);
if (x_1169 == 0)
{
return x_1164;
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1170 = lean_ctor_get(x_1164, 0);
x_1171 = lean_ctor_get(x_1164, 1);
lean_inc(x_1171);
lean_inc(x_1170);
lean_dec(x_1164);
x_1172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1172, 0, x_1170);
lean_ctor_set(x_1172, 1, x_1171);
return x_1172;
}
}
}
else
{
uint8_t x_1173; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_1173 = !lean_is_exclusive(x_1162);
if (x_1173 == 0)
{
return x_1162;
}
else
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1174 = lean_ctor_get(x_1162, 0);
x_1175 = lean_ctor_get(x_1162, 1);
lean_inc(x_1175);
lean_inc(x_1174);
lean_dec(x_1162);
x_1176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1176, 0, x_1174);
lean_ctor_set(x_1176, 1, x_1175);
return x_1176;
}
}
}
}
}
}
}
else
{
uint8_t x_1269; 
lean_free_object(x_1);
lean_dec(x_1120);
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
x_1269 = !lean_is_exclusive(x_1123);
if (x_1269 == 0)
{
return x_1123;
}
else
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1270 = lean_ctor_get(x_1123, 0);
x_1271 = lean_ctor_get(x_1123, 1);
lean_inc(x_1271);
lean_inc(x_1270);
lean_dec(x_1123);
x_1272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1272, 0, x_1270);
lean_ctor_set(x_1272, 1, x_1271);
return x_1272;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1273; lean_object* x_1274; 
x_1273 = lean_ctor_get(x_1123, 1);
lean_inc(x_1273);
lean_dec(x_1123);
if (x_1122 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1326; 
x_1326 = l_Lean_Expr_getOptParamDefault_x3f(x_94);
if (lean_obj_tag(x_1326) == 0)
{
lean_object* x_1327; 
x_1327 = l_Lean_Expr_getAutoParamTactic_x3f(x_94);
if (lean_obj_tag(x_1327) == 0)
{
lean_object* x_1328; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_1328 = lean_box(0);
x_1274 = x_1328;
goto block_1325;
}
else
{
lean_object* x_1329; 
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1329 = lean_ctor_get(x_1327, 0);
lean_inc(x_1329);
lean_dec(x_1327);
if (lean_obj_tag(x_1329) == 4)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
x_1330 = lean_ctor_get(x_1329, 0);
lean_inc(x_1330);
lean_dec(x_1329);
x_1331 = l_Lean_Elab_Term_getEnv___rarg(x_1273);
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1331, 1);
lean_inc(x_1333);
lean_dec(x_1331);
x_1334 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1332, x_1330);
if (lean_obj_tag(x_1334) == 0)
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
lean_dec(x_1334);
x_1336 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1336, 0, x_1335);
x_1337 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1337, 0, x_1336);
x_1338 = l_Lean_Elab_Term_throwError___rarg(x_1337, x_4, x_1333);
return x_1338;
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
x_1339 = lean_ctor_get(x_1334, 0);
lean_inc(x_1339);
lean_dec(x_1334);
x_1340 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1333);
x_1341 = lean_ctor_get(x_1340, 1);
lean_inc(x_1341);
lean_dec(x_1340);
x_1342 = l_Lean_Elab_Term_getMainModule___rarg(x_1341);
x_1343 = lean_ctor_get(x_1342, 1);
lean_inc(x_1343);
lean_dec(x_1342);
x_1344 = l_Lean_Syntax_getArgs(x_1339);
lean_dec(x_1339);
x_1345 = l_Array_empty___closed__1;
x_1346 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1344, x_1344, x_97, x_1345);
lean_dec(x_1344);
x_1347 = l_Lean_nullKind___closed__2;
x_1348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1348, 0, x_1347);
lean_ctor_set(x_1348, 1, x_1346);
x_1349 = lean_array_push(x_1345, x_1348);
x_1350 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_1351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1351, 0, x_1350);
lean_ctor_set(x_1351, 1, x_1349);
x_1352 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1353 = lean_array_push(x_1352, x_1351);
x_1354 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1355 = lean_array_push(x_1353, x_1354);
x_1356 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1357, 0, x_1356);
lean_ctor_set(x_1357, 1, x_1355);
x_1358 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_1359 = l_Lean_Expr_getAppNumArgsAux___main(x_94, x_97);
x_1360 = lean_nat_sub(x_1359, x_97);
lean_dec(x_1359);
x_1361 = lean_unsigned_to_nat(1u);
x_1362 = lean_nat_sub(x_1360, x_1361);
lean_dec(x_1360);
x_1363 = l_Lean_Expr_getRevArg_x21___main(x_94, x_1362);
lean_dec(x_94);
if (lean_obj_tag(x_1358) == 0)
{
lean_object* x_1364; lean_object* x_1365; 
x_1364 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1364, 0, x_1357);
lean_inc(x_4);
lean_inc(x_2);
x_1365 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1364, x_1363, x_4, x_1343);
if (lean_obj_tag(x_1365) == 0)
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1366 = lean_ctor_get(x_1365, 0);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1365, 1);
lean_inc(x_1367);
lean_dec(x_1365);
lean_inc(x_1366);
x_1368 = l_Lean_mkApp(x_2, x_1366);
x_1369 = lean_expr_instantiate1(x_95, x_1366);
lean_dec(x_1366);
lean_dec(x_95);
x_1 = x_1120;
x_2 = x_1368;
x_3 = x_1369;
x_5 = x_1367;
goto _start;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_1371 = lean_ctor_get(x_1365, 0);
lean_inc(x_1371);
x_1372 = lean_ctor_get(x_1365, 1);
lean_inc(x_1372);
if (lean_is_exclusive(x_1365)) {
 lean_ctor_release(x_1365, 0);
 lean_ctor_release(x_1365, 1);
 x_1373 = x_1365;
} else {
 lean_dec_ref(x_1365);
 x_1373 = lean_box(0);
}
if (lean_is_scalar(x_1373)) {
 x_1374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1374 = x_1373;
}
lean_ctor_set(x_1374, 0, x_1371);
lean_ctor_set(x_1374, 1, x_1372);
return x_1374;
}
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
x_1375 = lean_ctor_get(x_1358, 0);
lean_inc(x_1375);
lean_dec(x_1358);
x_1376 = l_Lean_Syntax_replaceInfo___main(x_1375, x_1357);
x_1377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1377, 0, x_1376);
lean_inc(x_4);
lean_inc(x_2);
x_1378 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1377, x_1363, x_4, x_1343);
if (lean_obj_tag(x_1378) == 0)
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; 
x_1379 = lean_ctor_get(x_1378, 0);
lean_inc(x_1379);
x_1380 = lean_ctor_get(x_1378, 1);
lean_inc(x_1380);
lean_dec(x_1378);
lean_inc(x_1379);
x_1381 = l_Lean_mkApp(x_2, x_1379);
x_1382 = lean_expr_instantiate1(x_95, x_1379);
lean_dec(x_1379);
lean_dec(x_95);
x_1 = x_1120;
x_2 = x_1381;
x_3 = x_1382;
x_5 = x_1380;
goto _start;
}
else
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_4);
lean_dec(x_2);
x_1384 = lean_ctor_get(x_1378, 0);
lean_inc(x_1384);
x_1385 = lean_ctor_get(x_1378, 1);
lean_inc(x_1385);
if (lean_is_exclusive(x_1378)) {
 lean_ctor_release(x_1378, 0);
 lean_ctor_release(x_1378, 1);
 x_1386 = x_1378;
} else {
 lean_dec_ref(x_1378);
 x_1386 = lean_box(0);
}
if (lean_is_scalar(x_1386)) {
 x_1387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1387 = x_1386;
}
lean_ctor_set(x_1387, 0, x_1384);
lean_ctor_set(x_1387, 1, x_1385);
return x_1387;
}
}
}
}
else
{
lean_object* x_1388; lean_object* x_1389; 
lean_dec(x_1329);
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_2);
x_1388 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1389 = l_Lean_Elab_Term_throwError___rarg(x_1388, x_4, x_1273);
return x_1389;
}
}
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1390 = lean_ctor_get(x_1326, 0);
lean_inc(x_1390);
lean_dec(x_1326);
lean_inc(x_1390);
x_1391 = l_Lean_mkApp(x_2, x_1390);
x_1392 = lean_expr_instantiate1(x_95, x_1390);
lean_dec(x_1390);
lean_dec(x_95);
x_1 = x_1120;
x_2 = x_1391;
x_3 = x_1392;
x_5 = x_1273;
goto _start;
}
}
else
{
lean_object* x_1394; 
lean_dec(x_1120);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
x_1394 = lean_box(0);
x_1274 = x_1394;
goto block_1325;
}
}
else
{
lean_object* x_1395; lean_object* x_1396; 
lean_dec(x_1120);
lean_dec(x_93);
lean_dec(x_3);
x_1395 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
x_1396 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1395, x_94, x_4, x_1273);
if (lean_obj_tag(x_1396) == 0)
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1397 = lean_ctor_get(x_1396, 0);
lean_inc(x_1397);
x_1398 = lean_ctor_get(x_1396, 1);
lean_inc(x_1398);
lean_dec(x_1396);
x_1399 = lean_unsigned_to_nat(1u);
x_1400 = lean_nat_add(x_10, x_1399);
lean_dec(x_10);
x_1401 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1401, 0, x_6);
lean_ctor_set(x_1401, 1, x_7);
lean_ctor_set(x_1401, 2, x_8);
lean_ctor_set(x_1401, 3, x_1400);
lean_ctor_set(x_1401, 4, x_11);
lean_ctor_set(x_1401, 5, x_12);
lean_ctor_set(x_1401, 6, x_13);
lean_ctor_set_uint8(x_1401, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1401, sizeof(void*)*7 + 1, x_1119);
lean_inc(x_1397);
x_1402 = l_Lean_mkApp(x_2, x_1397);
x_1403 = lean_expr_instantiate1(x_95, x_1397);
lean_dec(x_1397);
lean_dec(x_95);
x_1 = x_1401;
x_2 = x_1402;
x_3 = x_1403;
x_5 = x_1398;
goto _start;
}
else
{
lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; 
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
x_1405 = lean_ctor_get(x_1396, 0);
lean_inc(x_1405);
x_1406 = lean_ctor_get(x_1396, 1);
lean_inc(x_1406);
if (lean_is_exclusive(x_1396)) {
 lean_ctor_release(x_1396, 0);
 lean_ctor_release(x_1396, 1);
 x_1407 = x_1396;
} else {
 lean_dec_ref(x_1396);
 x_1407 = lean_box(0);
}
if (lean_is_scalar(x_1407)) {
 x_1408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1408 = x_1407;
}
lean_ctor_set(x_1408, 0, x_1405);
lean_ctor_set(x_1408, 1, x_1406);
return x_1408;
}
}
block_1325:
{
uint8_t x_1275; 
lean_dec(x_1274);
x_1275 = l_Array_isEmpty___rarg(x_11);
if (x_1275 == 0)
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1276 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1276, 0, x_93);
x_1277 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1278 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1278, 0, x_1277);
lean_ctor_set(x_1278, 1, x_1276);
x_1279 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1280 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1280, 0, x_1278);
lean_ctor_set(x_1280, 1, x_1279);
x_1281 = x_11;
x_1282 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_97, x_1281);
x_1283 = x_1282;
x_1284 = l_Array_toList___rarg(x_1283);
lean_dec(x_1283);
x_1285 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1284);
x_1286 = l_Array_HasRepr___rarg___closed__1;
x_1287 = lean_string_append(x_1286, x_1285);
lean_dec(x_1285);
x_1288 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1288, 0, x_1287);
x_1289 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1289, 0, x_1288);
x_1290 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1290, 0, x_1280);
lean_ctor_set(x_1290, 1, x_1289);
x_1291 = l_Lean_Elab_Term_throwError___rarg(x_1290, x_4, x_1273);
return x_1291;
}
else
{
lean_object* x_1292; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; uint8_t x_1321; 
lean_dec(x_93);
lean_dec(x_11);
x_1317 = l_Lean_Elab_Term_getOptions(x_4, x_1273);
x_1318 = lean_ctor_get(x_1317, 0);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1317, 1);
lean_inc(x_1319);
lean_dec(x_1317);
x_1320 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1321 = l_Lean_checkTraceOption(x_1318, x_1320);
lean_dec(x_1318);
if (x_1321 == 0)
{
x_1292 = x_1319;
goto block_1316;
}
else
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
lean_inc(x_2);
x_1322 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1322, 0, x_2);
x_1323 = l_Lean_Elab_Term_logTrace(x_1320, x_1322, x_4, x_1319);
x_1324 = lean_ctor_get(x_1323, 1);
lean_inc(x_1324);
lean_dec(x_1323);
x_1292 = x_1324;
goto block_1316;
}
block_1316:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1293; 
lean_dec(x_3);
x_1293 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_1292);
lean_dec(x_12);
if (lean_obj_tag(x_1293) == 0)
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1294 = lean_ctor_get(x_1293, 1);
lean_inc(x_1294);
if (lean_is_exclusive(x_1293)) {
 lean_ctor_release(x_1293, 0);
 lean_ctor_release(x_1293, 1);
 x_1295 = x_1293;
} else {
 lean_dec_ref(x_1293);
 x_1295 = lean_box(0);
}
if (lean_is_scalar(x_1295)) {
 x_1296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1296 = x_1295;
}
lean_ctor_set(x_1296, 0, x_2);
lean_ctor_set(x_1296, 1, x_1294);
return x_1296;
}
else
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
lean_dec(x_2);
x_1297 = lean_ctor_get(x_1293, 0);
lean_inc(x_1297);
x_1298 = lean_ctor_get(x_1293, 1);
lean_inc(x_1298);
if (lean_is_exclusive(x_1293)) {
 lean_ctor_release(x_1293, 0);
 lean_ctor_release(x_1293, 1);
 x_1299 = x_1293;
} else {
 lean_dec_ref(x_1293);
 x_1299 = lean_box(0);
}
if (lean_is_scalar(x_1299)) {
 x_1300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1300 = x_1299;
}
lean_ctor_set(x_1300, 0, x_1297);
lean_ctor_set(x_1300, 1, x_1298);
return x_1300;
}
}
else
{
lean_object* x_1301; lean_object* x_1302; 
x_1301 = lean_ctor_get(x_8, 0);
lean_inc(x_1301);
lean_dec(x_8);
lean_inc(x_4);
x_1302 = l_Lean_Elab_Term_isDefEq(x_1301, x_3, x_4, x_1292);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; lean_object* x_1304; 
x_1303 = lean_ctor_get(x_1302, 1);
lean_inc(x_1303);
lean_dec(x_1302);
x_1304 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_97, x_4, x_1303);
lean_dec(x_12);
if (lean_obj_tag(x_1304) == 0)
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
x_1305 = lean_ctor_get(x_1304, 1);
lean_inc(x_1305);
if (lean_is_exclusive(x_1304)) {
 lean_ctor_release(x_1304, 0);
 lean_ctor_release(x_1304, 1);
 x_1306 = x_1304;
} else {
 lean_dec_ref(x_1304);
 x_1306 = lean_box(0);
}
if (lean_is_scalar(x_1306)) {
 x_1307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1307 = x_1306;
}
lean_ctor_set(x_1307, 0, x_2);
lean_ctor_set(x_1307, 1, x_1305);
return x_1307;
}
else
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
lean_dec(x_2);
x_1308 = lean_ctor_get(x_1304, 0);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1304, 1);
lean_inc(x_1309);
if (lean_is_exclusive(x_1304)) {
 lean_ctor_release(x_1304, 0);
 lean_ctor_release(x_1304, 1);
 x_1310 = x_1304;
} else {
 lean_dec_ref(x_1304);
 x_1310 = lean_box(0);
}
if (lean_is_scalar(x_1310)) {
 x_1311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1311 = x_1310;
}
lean_ctor_set(x_1311, 0, x_1308);
lean_ctor_set(x_1311, 1, x_1309);
return x_1311;
}
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_1312 = lean_ctor_get(x_1302, 0);
lean_inc(x_1312);
x_1313 = lean_ctor_get(x_1302, 1);
lean_inc(x_1313);
if (lean_is_exclusive(x_1302)) {
 lean_ctor_release(x_1302, 0);
 lean_ctor_release(x_1302, 1);
 x_1314 = x_1302;
} else {
 lean_dec_ref(x_1302);
 x_1314 = lean_box(0);
}
if (lean_is_scalar(x_1314)) {
 x_1315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1315 = x_1314;
}
lean_ctor_set(x_1315, 0, x_1312);
lean_ctor_set(x_1315, 1, x_1313);
return x_1315;
}
}
}
}
}
}
else
{
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
lean_dec(x_1120);
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
x_1409 = lean_ctor_get(x_1123, 0);
lean_inc(x_1409);
x_1410 = lean_ctor_get(x_1123, 1);
lean_inc(x_1410);
if (lean_is_exclusive(x_1123)) {
 lean_ctor_release(x_1123, 0);
 lean_ctor_release(x_1123, 1);
 x_1411 = x_1123;
} else {
 lean_dec_ref(x_1123);
 x_1411 = lean_box(0);
}
if (lean_is_scalar(x_1411)) {
 x_1412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1412 = x_1411;
}
lean_ctor_set(x_1412, 0, x_1409);
lean_ctor_set(x_1412, 1, x_1410);
return x_1412;
}
}
}
}
}
else
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; 
lean_dec(x_93);
lean_dec(x_3);
x_1413 = lean_ctor_get(x_98, 0);
lean_inc(x_1413);
lean_dec(x_98);
x_1414 = l_Lean_Elab_Term_NamedArg_inhabited;
x_1415 = lean_array_get(x_1414, x_11, x_1413);
x_1416 = l_Array_eraseIdx___rarg(x_11, x_1413);
lean_dec(x_1413);
x_1417 = lean_ctor_get(x_1415, 1);
lean_inc(x_1417);
lean_dec(x_1415);
lean_inc(x_4);
lean_inc(x_2);
x_1418 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1417, x_94, x_4, x_20);
if (lean_obj_tag(x_1418) == 0)
{
lean_object* x_1419; lean_object* x_1420; uint8_t x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; 
x_1419 = lean_ctor_get(x_1418, 0);
lean_inc(x_1419);
x_1420 = lean_ctor_get(x_1418, 1);
lean_inc(x_1420);
lean_dec(x_1418);
x_1421 = 1;
x_1422 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1422, 0, x_6);
lean_ctor_set(x_1422, 1, x_7);
lean_ctor_set(x_1422, 2, x_8);
lean_ctor_set(x_1422, 3, x_10);
lean_ctor_set(x_1422, 4, x_1416);
lean_ctor_set(x_1422, 5, x_12);
lean_ctor_set(x_1422, 6, x_13);
lean_ctor_set_uint8(x_1422, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1422, sizeof(void*)*7 + 1, x_1421);
lean_inc(x_1419);
x_1423 = l_Lean_mkApp(x_2, x_1419);
x_1424 = lean_expr_instantiate1(x_95, x_1419);
lean_dec(x_1419);
lean_dec(x_95);
lean_inc(x_4);
x_1425 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_19, x_4, x_1420);
if (lean_obj_tag(x_1425) == 0)
{
lean_object* x_1426; 
x_1426 = lean_ctor_get(x_1425, 1);
lean_inc(x_1426);
lean_dec(x_1425);
x_1 = x_1422;
x_2 = x_1423;
x_3 = x_1424;
x_5 = x_1426;
goto _start;
}
else
{
uint8_t x_1428; 
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_1422);
lean_dec(x_4);
x_1428 = !lean_is_exclusive(x_1425);
if (x_1428 == 0)
{
return x_1425;
}
else
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; 
x_1429 = lean_ctor_get(x_1425, 0);
x_1430 = lean_ctor_get(x_1425, 1);
lean_inc(x_1430);
lean_inc(x_1429);
lean_dec(x_1425);
x_1431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1431, 0, x_1429);
lean_ctor_set(x_1431, 1, x_1430);
return x_1431;
}
}
}
else
{
uint8_t x_1432; 
lean_dec(x_1416);
lean_dec(x_95);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_1432 = !lean_is_exclusive(x_1418);
if (x_1432 == 0)
{
return x_1418;
}
else
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
x_1433 = lean_ctor_get(x_1418, 0);
x_1434 = lean_ctor_get(x_1418, 1);
lean_inc(x_1434);
lean_inc(x_1433);
lean_dec(x_1418);
x_1435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1435, 0, x_1433);
lean_ctor_set(x_1435, 1, x_1434);
return x_1435;
}
}
}
}
else
{
lean_object* x_1436; 
lean_dec(x_13);
lean_dec(x_6);
x_1436 = lean_box(0);
x_21 = x_1436;
goto block_92;
}
block_92:
{
uint8_t x_22; 
lean_dec(x_21);
x_22 = l_Array_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_inc(x_4);
x_23 = l___private_Lean_Elab_App_4__tryCoeFun(x_19, x_2, x_4, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_4);
lean_inc(x_24);
x_26 = l_Lean_Elab_Term_inferType(x_24, x_4, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_2 = x_24;
x_3 = x_27;
x_5 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_4);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_array_get_size(x_7);
lean_dec(x_7);
x_39 = lean_nat_dec_eq(x_10, x_38);
lean_dec(x_38);
lean_dec(x_10);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_inc(x_4);
x_40 = l___private_Lean_Elab_App_4__tryCoeFun(x_19, x_2, x_4, x_20);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_4);
lean_inc(x_41);
x_43 = l_Lean_Elab_Term_inferType(x_41, x_4, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_2 = x_41;
x_3 = x_44;
x_5 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_4);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_4);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_19);
lean_dec(x_1);
x_84 = l_Lean_Elab_Term_getOptions(x_4, x_20);
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
x_55 = x_86;
goto block_83;
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
x_55 = x_91;
goto block_83;
}
block_83:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_3);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_56, x_4, x_55);
lean_dec(x_12);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_2);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_8, 0);
lean_inc(x_66);
lean_dec(x_8);
lean_inc(x_4);
x_67 = l_Lean_Elab_Term_isDefEq(x_66, x_3, x_4, x_55);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_69, x_4, x_68);
lean_dec(x_12);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_2);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 0);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_70);
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
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_67);
if (x_79 == 0)
{
return x_67;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_67, 0);
x_81 = lean_ctor_get(x_67, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_67);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
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
uint8_t x_1437; 
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
x_1437 = !lean_is_exclusive(x_18);
if (x_1437 == 0)
{
return x_18;
}
else
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
x_1438 = lean_ctor_get(x_18, 0);
x_1439 = lean_ctor_get(x_18, 1);
lean_inc(x_1439);
lean_inc(x_1438);
lean_dec(x_18);
x_1440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1440, 0, x_1438);
lean_ctor_set(x_1440, 1, x_1439);
return x_1440;
}
}
}
else
{
uint8_t x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; uint8_t x_1451; uint8_t x_1452; uint8_t x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
x_1441 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_1442 = lean_ctor_get(x_4, 0);
x_1443 = lean_ctor_get(x_4, 1);
x_1444 = lean_ctor_get(x_4, 2);
x_1445 = lean_ctor_get(x_4, 3);
x_1446 = lean_ctor_get(x_4, 4);
x_1447 = lean_ctor_get(x_4, 5);
x_1448 = lean_ctor_get(x_4, 6);
x_1449 = lean_ctor_get(x_4, 7);
x_1450 = lean_ctor_get(x_4, 8);
x_1451 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_1452 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_1453 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_1454 = lean_ctor_get(x_4, 9);
lean_inc(x_1454);
lean_inc(x_1450);
lean_inc(x_1449);
lean_inc(x_1448);
lean_inc(x_1447);
lean_inc(x_1446);
lean_inc(x_1445);
lean_inc(x_1444);
lean_inc(x_1443);
lean_inc(x_1442);
lean_dec(x_4);
x_1455 = l_Lean_Elab_replaceRef(x_6, x_1454);
lean_dec(x_1454);
x_1456 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_1456, 0, x_1442);
lean_ctor_set(x_1456, 1, x_1443);
lean_ctor_set(x_1456, 2, x_1444);
lean_ctor_set(x_1456, 3, x_1445);
lean_ctor_set(x_1456, 4, x_1446);
lean_ctor_set(x_1456, 5, x_1447);
lean_ctor_set(x_1456, 6, x_1448);
lean_ctor_set(x_1456, 7, x_1449);
lean_ctor_set(x_1456, 8, x_1450);
lean_ctor_set(x_1456, 9, x_1455);
lean_ctor_set_uint8(x_1456, sizeof(void*)*10, x_1451);
lean_ctor_set_uint8(x_1456, sizeof(void*)*10 + 1, x_1452);
lean_ctor_set_uint8(x_1456, sizeof(void*)*10 + 2, x_1453);
lean_inc(x_1456);
lean_inc(x_3);
x_1457 = l_Lean_Elab_Term_whnfForall(x_3, x_1456, x_5);
if (lean_obj_tag(x_1457) == 0)
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
x_1458 = lean_ctor_get(x_1457, 0);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1457, 1);
lean_inc(x_1459);
lean_dec(x_1457);
if (lean_obj_tag(x_1458) == 7)
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; uint64_t x_1533; lean_object* x_1534; lean_object* x_1535; 
x_1530 = lean_ctor_get(x_1458, 0);
lean_inc(x_1530);
x_1531 = lean_ctor_get(x_1458, 1);
lean_inc(x_1531);
x_1532 = lean_ctor_get(x_1458, 2);
lean_inc(x_1532);
x_1533 = lean_ctor_get_uint64(x_1458, sizeof(void*)*3);
x_1534 = lean_unsigned_to_nat(0u);
x_1535 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_1530, x_11, x_1534);
if (lean_obj_tag(x_1535) == 0)
{
uint8_t x_1536; 
x_1536 = (uint8_t)((x_1533 << 24) >> 61);
switch (x_1536) {
case 0:
{
uint8_t x_1537; lean_object* x_1538; lean_object* x_1539; uint8_t x_1540; lean_object* x_1541; lean_object* x_1542; 
x_1537 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1538 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1538, 0, x_6);
lean_ctor_set(x_1538, 1, x_7);
lean_ctor_set(x_1538, 2, x_8);
lean_ctor_set(x_1538, 3, x_10);
lean_ctor_set(x_1538, 4, x_11);
lean_ctor_set(x_1538, 5, x_12);
lean_ctor_set(x_1538, 6, x_13);
lean_ctor_set_uint8(x_1538, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1538, sizeof(void*)*7 + 1, x_1537);
x_1539 = lean_array_get_size(x_7);
x_1540 = lean_nat_dec_lt(x_10, x_1539);
lean_dec(x_1539);
lean_inc(x_1456);
lean_inc(x_1);
x_1541 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1458, x_1456, x_1459);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1542 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1542 = lean_box(0);
}
if (lean_obj_tag(x_1541) == 0)
{
lean_object* x_1543; lean_object* x_1544; 
x_1543 = lean_ctor_get(x_1541, 1);
lean_inc(x_1543);
lean_dec(x_1541);
if (x_1540 == 0)
{
lean_dec(x_1542);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1596; 
x_1596 = l_Lean_Expr_getOptParamDefault_x3f(x_1531);
if (lean_obj_tag(x_1596) == 0)
{
lean_object* x_1597; 
x_1597 = l_Lean_Expr_getAutoParamTactic_x3f(x_1531);
if (lean_obj_tag(x_1597) == 0)
{
lean_object* x_1598; 
lean_dec(x_1538);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
x_1598 = lean_box(0);
x_1544 = x_1598;
goto block_1595;
}
else
{
lean_object* x_1599; 
lean_dec(x_1530);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1599 = lean_ctor_get(x_1597, 0);
lean_inc(x_1599);
lean_dec(x_1597);
if (lean_obj_tag(x_1599) == 4)
{
lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; 
x_1600 = lean_ctor_get(x_1599, 0);
lean_inc(x_1600);
lean_dec(x_1599);
x_1601 = l_Lean_Elab_Term_getEnv___rarg(x_1543);
x_1602 = lean_ctor_get(x_1601, 0);
lean_inc(x_1602);
x_1603 = lean_ctor_get(x_1601, 1);
lean_inc(x_1603);
lean_dec(x_1601);
x_1604 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1602, x_1600);
if (lean_obj_tag(x_1604) == 0)
{
lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; 
lean_dec(x_1538);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
lean_dec(x_2);
x_1605 = lean_ctor_get(x_1604, 0);
lean_inc(x_1605);
lean_dec(x_1604);
x_1606 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1606, 0, x_1605);
x_1607 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1607, 0, x_1606);
x_1608 = l_Lean_Elab_Term_throwError___rarg(x_1607, x_1456, x_1603);
return x_1608;
}
else
{
lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; 
x_1609 = lean_ctor_get(x_1604, 0);
lean_inc(x_1609);
lean_dec(x_1604);
x_1610 = l_Lean_Elab_Term_getCurrMacroScope(x_1456, x_1603);
x_1611 = lean_ctor_get(x_1610, 1);
lean_inc(x_1611);
lean_dec(x_1610);
x_1612 = l_Lean_Elab_Term_getMainModule___rarg(x_1611);
x_1613 = lean_ctor_get(x_1612, 1);
lean_inc(x_1613);
lean_dec(x_1612);
x_1614 = l_Lean_Syntax_getArgs(x_1609);
lean_dec(x_1609);
x_1615 = l_Array_empty___closed__1;
x_1616 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1614, x_1614, x_1534, x_1615);
lean_dec(x_1614);
x_1617 = l_Lean_nullKind___closed__2;
x_1618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1618, 0, x_1617);
lean_ctor_set(x_1618, 1, x_1616);
x_1619 = lean_array_push(x_1615, x_1618);
x_1620 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_1621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1621, 0, x_1620);
lean_ctor_set(x_1621, 1, x_1619);
x_1622 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1623 = lean_array_push(x_1622, x_1621);
x_1624 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1625 = lean_array_push(x_1623, x_1624);
x_1626 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1627, 0, x_1626);
lean_ctor_set(x_1627, 1, x_1625);
x_1628 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_1629 = l_Lean_Expr_getAppNumArgsAux___main(x_1531, x_1534);
x_1630 = lean_nat_sub(x_1629, x_1534);
lean_dec(x_1629);
x_1631 = lean_unsigned_to_nat(1u);
x_1632 = lean_nat_sub(x_1630, x_1631);
lean_dec(x_1630);
x_1633 = l_Lean_Expr_getRevArg_x21___main(x_1531, x_1632);
lean_dec(x_1531);
if (lean_obj_tag(x_1628) == 0)
{
lean_object* x_1634; lean_object* x_1635; 
x_1634 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1634, 0, x_1627);
lean_inc(x_1456);
lean_inc(x_2);
x_1635 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1634, x_1633, x_1456, x_1613);
if (lean_obj_tag(x_1635) == 0)
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; 
x_1636 = lean_ctor_get(x_1635, 0);
lean_inc(x_1636);
x_1637 = lean_ctor_get(x_1635, 1);
lean_inc(x_1637);
lean_dec(x_1635);
lean_inc(x_1636);
x_1638 = l_Lean_mkApp(x_2, x_1636);
x_1639 = lean_expr_instantiate1(x_1532, x_1636);
lean_dec(x_1636);
lean_dec(x_1532);
x_1 = x_1538;
x_2 = x_1638;
x_3 = x_1639;
x_4 = x_1456;
x_5 = x_1637;
goto _start;
}
else
{
lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; 
lean_dec(x_1538);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_2);
x_1641 = lean_ctor_get(x_1635, 0);
lean_inc(x_1641);
x_1642 = lean_ctor_get(x_1635, 1);
lean_inc(x_1642);
if (lean_is_exclusive(x_1635)) {
 lean_ctor_release(x_1635, 0);
 lean_ctor_release(x_1635, 1);
 x_1643 = x_1635;
} else {
 lean_dec_ref(x_1635);
 x_1643 = lean_box(0);
}
if (lean_is_scalar(x_1643)) {
 x_1644 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1644 = x_1643;
}
lean_ctor_set(x_1644, 0, x_1641);
lean_ctor_set(x_1644, 1, x_1642);
return x_1644;
}
}
else
{
lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; 
x_1645 = lean_ctor_get(x_1628, 0);
lean_inc(x_1645);
lean_dec(x_1628);
x_1646 = l_Lean_Syntax_replaceInfo___main(x_1645, x_1627);
x_1647 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1647, 0, x_1646);
lean_inc(x_1456);
lean_inc(x_2);
x_1648 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1647, x_1633, x_1456, x_1613);
if (lean_obj_tag(x_1648) == 0)
{
lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; 
x_1649 = lean_ctor_get(x_1648, 0);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_1648, 1);
lean_inc(x_1650);
lean_dec(x_1648);
lean_inc(x_1649);
x_1651 = l_Lean_mkApp(x_2, x_1649);
x_1652 = lean_expr_instantiate1(x_1532, x_1649);
lean_dec(x_1649);
lean_dec(x_1532);
x_1 = x_1538;
x_2 = x_1651;
x_3 = x_1652;
x_4 = x_1456;
x_5 = x_1650;
goto _start;
}
else
{
lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; 
lean_dec(x_1538);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_2);
x_1654 = lean_ctor_get(x_1648, 0);
lean_inc(x_1654);
x_1655 = lean_ctor_get(x_1648, 1);
lean_inc(x_1655);
if (lean_is_exclusive(x_1648)) {
 lean_ctor_release(x_1648, 0);
 lean_ctor_release(x_1648, 1);
 x_1656 = x_1648;
} else {
 lean_dec_ref(x_1648);
 x_1656 = lean_box(0);
}
if (lean_is_scalar(x_1656)) {
 x_1657 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1657 = x_1656;
}
lean_ctor_set(x_1657, 0, x_1654);
lean_ctor_set(x_1657, 1, x_1655);
return x_1657;
}
}
}
}
else
{
lean_object* x_1658; lean_object* x_1659; 
lean_dec(x_1599);
lean_dec(x_1538);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
lean_dec(x_2);
x_1658 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1659 = l_Lean_Elab_Term_throwError___rarg(x_1658, x_1456, x_1543);
return x_1659;
}
}
}
else
{
lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; 
lean_dec(x_1531);
lean_dec(x_1530);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1660 = lean_ctor_get(x_1596, 0);
lean_inc(x_1660);
lean_dec(x_1596);
lean_inc(x_1660);
x_1661 = l_Lean_mkApp(x_2, x_1660);
x_1662 = lean_expr_instantiate1(x_1532, x_1660);
lean_dec(x_1660);
lean_dec(x_1532);
x_1 = x_1538;
x_2 = x_1661;
x_3 = x_1662;
x_4 = x_1456;
x_5 = x_1543;
goto _start;
}
}
else
{
lean_object* x_1664; 
lean_dec(x_1538);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
x_1664 = lean_box(0);
x_1544 = x_1664;
goto block_1595;
}
}
else
{
lean_object* x_1665; lean_object* x_1666; 
lean_dec(x_1538);
lean_dec(x_1530);
lean_dec(x_3);
x_1665 = lean_array_fget(x_7, x_10);
lean_inc(x_1456);
lean_inc(x_2);
x_1666 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1665, x_1531, x_1456, x_1543);
if (lean_obj_tag(x_1666) == 0)
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; 
x_1667 = lean_ctor_get(x_1666, 0);
lean_inc(x_1667);
x_1668 = lean_ctor_get(x_1666, 1);
lean_inc(x_1668);
lean_dec(x_1666);
x_1669 = lean_unsigned_to_nat(1u);
x_1670 = lean_nat_add(x_10, x_1669);
lean_dec(x_10);
if (lean_is_scalar(x_1542)) {
 x_1671 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1671 = x_1542;
}
lean_ctor_set(x_1671, 0, x_6);
lean_ctor_set(x_1671, 1, x_7);
lean_ctor_set(x_1671, 2, x_8);
lean_ctor_set(x_1671, 3, x_1670);
lean_ctor_set(x_1671, 4, x_11);
lean_ctor_set(x_1671, 5, x_12);
lean_ctor_set(x_1671, 6, x_13);
lean_ctor_set_uint8(x_1671, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1671, sizeof(void*)*7 + 1, x_1537);
lean_inc(x_1667);
x_1672 = l_Lean_mkApp(x_2, x_1667);
x_1673 = lean_expr_instantiate1(x_1532, x_1667);
lean_dec(x_1667);
lean_dec(x_1532);
x_1 = x_1671;
x_2 = x_1672;
x_3 = x_1673;
x_4 = x_1456;
x_5 = x_1668;
goto _start;
}
else
{
lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; 
lean_dec(x_1542);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1675 = lean_ctor_get(x_1666, 0);
lean_inc(x_1675);
x_1676 = lean_ctor_get(x_1666, 1);
lean_inc(x_1676);
if (lean_is_exclusive(x_1666)) {
 lean_ctor_release(x_1666, 0);
 lean_ctor_release(x_1666, 1);
 x_1677 = x_1666;
} else {
 lean_dec_ref(x_1666);
 x_1677 = lean_box(0);
}
if (lean_is_scalar(x_1677)) {
 x_1678 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1678 = x_1677;
}
lean_ctor_set(x_1678, 0, x_1675);
lean_ctor_set(x_1678, 1, x_1676);
return x_1678;
}
}
block_1595:
{
uint8_t x_1545; 
lean_dec(x_1544);
x_1545 = l_Array_isEmpty___rarg(x_11);
if (x_1545 == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1546 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1546, 0, x_1530);
x_1547 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1548 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1548, 0, x_1547);
lean_ctor_set(x_1548, 1, x_1546);
x_1549 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1550 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1550, 0, x_1548);
lean_ctor_set(x_1550, 1, x_1549);
x_1551 = x_11;
x_1552 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1534, x_1551);
x_1553 = x_1552;
x_1554 = l_Array_toList___rarg(x_1553);
lean_dec(x_1553);
x_1555 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1554);
x_1556 = l_Array_HasRepr___rarg___closed__1;
x_1557 = lean_string_append(x_1556, x_1555);
lean_dec(x_1555);
x_1558 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1558, 0, x_1557);
x_1559 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1559, 0, x_1558);
x_1560 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1560, 0, x_1550);
lean_ctor_set(x_1560, 1, x_1559);
x_1561 = l_Lean_Elab_Term_throwError___rarg(x_1560, x_1456, x_1543);
return x_1561;
}
else
{
lean_object* x_1562; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; uint8_t x_1591; 
lean_dec(x_1530);
lean_dec(x_11);
x_1587 = l_Lean_Elab_Term_getOptions(x_1456, x_1543);
x_1588 = lean_ctor_get(x_1587, 0);
lean_inc(x_1588);
x_1589 = lean_ctor_get(x_1587, 1);
lean_inc(x_1589);
lean_dec(x_1587);
x_1590 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1591 = l_Lean_checkTraceOption(x_1588, x_1590);
lean_dec(x_1588);
if (x_1591 == 0)
{
x_1562 = x_1589;
goto block_1586;
}
else
{
lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; 
lean_inc(x_2);
x_1592 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1592, 0, x_2);
x_1593 = l_Lean_Elab_Term_logTrace(x_1590, x_1592, x_1456, x_1589);
x_1594 = lean_ctor_get(x_1593, 1);
lean_inc(x_1594);
lean_dec(x_1593);
x_1562 = x_1594;
goto block_1586;
}
block_1586:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1563; 
lean_dec(x_3);
x_1563 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_1562);
lean_dec(x_12);
if (lean_obj_tag(x_1563) == 0)
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; 
x_1564 = lean_ctor_get(x_1563, 1);
lean_inc(x_1564);
if (lean_is_exclusive(x_1563)) {
 lean_ctor_release(x_1563, 0);
 lean_ctor_release(x_1563, 1);
 x_1565 = x_1563;
} else {
 lean_dec_ref(x_1563);
 x_1565 = lean_box(0);
}
if (lean_is_scalar(x_1565)) {
 x_1566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1566 = x_1565;
}
lean_ctor_set(x_1566, 0, x_2);
lean_ctor_set(x_1566, 1, x_1564);
return x_1566;
}
else
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
lean_dec(x_2);
x_1567 = lean_ctor_get(x_1563, 0);
lean_inc(x_1567);
x_1568 = lean_ctor_get(x_1563, 1);
lean_inc(x_1568);
if (lean_is_exclusive(x_1563)) {
 lean_ctor_release(x_1563, 0);
 lean_ctor_release(x_1563, 1);
 x_1569 = x_1563;
} else {
 lean_dec_ref(x_1563);
 x_1569 = lean_box(0);
}
if (lean_is_scalar(x_1569)) {
 x_1570 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1570 = x_1569;
}
lean_ctor_set(x_1570, 0, x_1567);
lean_ctor_set(x_1570, 1, x_1568);
return x_1570;
}
}
else
{
lean_object* x_1571; lean_object* x_1572; 
x_1571 = lean_ctor_get(x_8, 0);
lean_inc(x_1571);
lean_dec(x_8);
lean_inc(x_1456);
x_1572 = l_Lean_Elab_Term_isDefEq(x_1571, x_3, x_1456, x_1562);
if (lean_obj_tag(x_1572) == 0)
{
lean_object* x_1573; lean_object* x_1574; 
x_1573 = lean_ctor_get(x_1572, 1);
lean_inc(x_1573);
lean_dec(x_1572);
x_1574 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_1573);
lean_dec(x_12);
if (lean_obj_tag(x_1574) == 0)
{
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; 
x_1575 = lean_ctor_get(x_1574, 1);
lean_inc(x_1575);
if (lean_is_exclusive(x_1574)) {
 lean_ctor_release(x_1574, 0);
 lean_ctor_release(x_1574, 1);
 x_1576 = x_1574;
} else {
 lean_dec_ref(x_1574);
 x_1576 = lean_box(0);
}
if (lean_is_scalar(x_1576)) {
 x_1577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1577 = x_1576;
}
lean_ctor_set(x_1577, 0, x_2);
lean_ctor_set(x_1577, 1, x_1575);
return x_1577;
}
else
{
lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; 
lean_dec(x_2);
x_1578 = lean_ctor_get(x_1574, 0);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_1574, 1);
lean_inc(x_1579);
if (lean_is_exclusive(x_1574)) {
 lean_ctor_release(x_1574, 0);
 lean_ctor_release(x_1574, 1);
 x_1580 = x_1574;
} else {
 lean_dec_ref(x_1574);
 x_1580 = lean_box(0);
}
if (lean_is_scalar(x_1580)) {
 x_1581 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1581 = x_1580;
}
lean_ctor_set(x_1581, 0, x_1578);
lean_ctor_set(x_1581, 1, x_1579);
return x_1581;
}
}
else
{
lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; 
lean_dec(x_1456);
lean_dec(x_12);
lean_dec(x_2);
x_1582 = lean_ctor_get(x_1572, 0);
lean_inc(x_1582);
x_1583 = lean_ctor_get(x_1572, 1);
lean_inc(x_1583);
if (lean_is_exclusive(x_1572)) {
 lean_ctor_release(x_1572, 0);
 lean_ctor_release(x_1572, 1);
 x_1584 = x_1572;
} else {
 lean_dec_ref(x_1572);
 x_1584 = lean_box(0);
}
if (lean_is_scalar(x_1584)) {
 x_1585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1585 = x_1584;
}
lean_ctor_set(x_1585, 0, x_1582);
lean_ctor_set(x_1585, 1, x_1583);
return x_1585;
}
}
}
}
}
}
else
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; 
lean_dec(x_1542);
lean_dec(x_1538);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_1530);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_1679 = lean_ctor_get(x_1541, 0);
lean_inc(x_1679);
x_1680 = lean_ctor_get(x_1541, 1);
lean_inc(x_1680);
if (lean_is_exclusive(x_1541)) {
 lean_ctor_release(x_1541, 0);
 lean_ctor_release(x_1541, 1);
 x_1681 = x_1541;
} else {
 lean_dec_ref(x_1541);
 x_1681 = lean_box(0);
}
if (lean_is_scalar(x_1681)) {
 x_1682 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1682 = x_1681;
}
lean_ctor_set(x_1682, 0, x_1679);
lean_ctor_set(x_1682, 1, x_1680);
return x_1682;
}
}
case 1:
{
if (x_9 == 0)
{
lean_object* x_1683; lean_object* x_1684; uint8_t x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; 
lean_dec(x_1530);
lean_dec(x_1458);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1683 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1683 = lean_box(0);
}
x_1684 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1684, 0, x_1531);
x_1685 = 0;
x_1686 = lean_box(0);
lean_inc(x_1456);
x_1687 = l_Lean_Elab_Term_mkFreshExprMVar(x_1684, x_1685, x_1686, x_1456, x_1459);
x_1688 = lean_ctor_get(x_1687, 0);
lean_inc(x_1688);
x_1689 = lean_ctor_get(x_1687, 1);
lean_inc(x_1689);
lean_dec(x_1687);
lean_inc(x_1456);
lean_inc(x_1688);
x_1690 = l_Lean_Elab_Term_isTypeFormer(x_1688, x_1456, x_1689);
if (lean_obj_tag(x_1690) == 0)
{
lean_object* x_1691; uint8_t x_1692; 
x_1691 = lean_ctor_get(x_1690, 0);
lean_inc(x_1691);
x_1692 = lean_unbox(x_1691);
lean_dec(x_1691);
if (x_1692 == 0)
{
lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; 
x_1693 = lean_ctor_get(x_1690, 1);
lean_inc(x_1693);
lean_dec(x_1690);
if (lean_is_scalar(x_1683)) {
 x_1694 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1694 = x_1683;
}
lean_ctor_set(x_1694, 0, x_6);
lean_ctor_set(x_1694, 1, x_7);
lean_ctor_set(x_1694, 2, x_8);
lean_ctor_set(x_1694, 3, x_10);
lean_ctor_set(x_1694, 4, x_11);
lean_ctor_set(x_1694, 5, x_12);
lean_ctor_set(x_1694, 6, x_13);
lean_ctor_set_uint8(x_1694, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1694, sizeof(void*)*7 + 1, x_1441);
lean_inc(x_1688);
x_1695 = l_Lean_mkApp(x_2, x_1688);
x_1696 = lean_expr_instantiate1(x_1532, x_1688);
lean_dec(x_1688);
lean_dec(x_1532);
x_1 = x_1694;
x_2 = x_1695;
x_3 = x_1696;
x_4 = x_1456;
x_5 = x_1693;
goto _start;
}
else
{
lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; 
x_1698 = lean_ctor_get(x_1690, 1);
lean_inc(x_1698);
lean_dec(x_1690);
x_1699 = l_Lean_Expr_mvarId_x21(x_1688);
x_1700 = lean_array_push(x_13, x_1699);
if (lean_is_scalar(x_1683)) {
 x_1701 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1701 = x_1683;
}
lean_ctor_set(x_1701, 0, x_6);
lean_ctor_set(x_1701, 1, x_7);
lean_ctor_set(x_1701, 2, x_8);
lean_ctor_set(x_1701, 3, x_10);
lean_ctor_set(x_1701, 4, x_11);
lean_ctor_set(x_1701, 5, x_12);
lean_ctor_set(x_1701, 6, x_1700);
lean_ctor_set_uint8(x_1701, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1701, sizeof(void*)*7 + 1, x_1441);
lean_inc(x_1688);
x_1702 = l_Lean_mkApp(x_2, x_1688);
x_1703 = lean_expr_instantiate1(x_1532, x_1688);
lean_dec(x_1688);
lean_dec(x_1532);
x_1 = x_1701;
x_2 = x_1702;
x_3 = x_1703;
x_4 = x_1456;
x_5 = x_1698;
goto _start;
}
}
else
{
lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; 
lean_dec(x_1688);
lean_dec(x_1683);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1705 = lean_ctor_get(x_1690, 0);
lean_inc(x_1705);
x_1706 = lean_ctor_get(x_1690, 1);
lean_inc(x_1706);
if (lean_is_exclusive(x_1690)) {
 lean_ctor_release(x_1690, 0);
 lean_ctor_release(x_1690, 1);
 x_1707 = x_1690;
} else {
 lean_dec_ref(x_1690);
 x_1707 = lean_box(0);
}
if (lean_is_scalar(x_1707)) {
 x_1708 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1708 = x_1707;
}
lean_ctor_set(x_1708, 0, x_1705);
lean_ctor_set(x_1708, 1, x_1706);
return x_1708;
}
}
else
{
lean_object* x_1709; uint8_t x_1710; lean_object* x_1711; lean_object* x_1712; 
x_1709 = lean_array_get_size(x_7);
x_1710 = lean_nat_dec_lt(x_10, x_1709);
lean_dec(x_1709);
lean_inc(x_1456);
lean_inc(x_1);
x_1711 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1458, x_1456, x_1459);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1712 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1712 = lean_box(0);
}
if (lean_obj_tag(x_1711) == 0)
{
if (x_1710 == 0)
{
lean_object* x_1713; uint8_t x_1714; 
lean_dec(x_1712);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_1713 = lean_ctor_get(x_1711, 1);
lean_inc(x_1713);
lean_dec(x_1711);
x_1714 = l_Array_isEmpty___rarg(x_11);
if (x_1714 == 0)
{
lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1715 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1715, 0, x_1530);
x_1716 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1717 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1717, 0, x_1716);
lean_ctor_set(x_1717, 1, x_1715);
x_1718 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1719 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1719, 0, x_1717);
lean_ctor_set(x_1719, 1, x_1718);
x_1720 = x_11;
x_1721 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1534, x_1720);
x_1722 = x_1721;
x_1723 = l_Array_toList___rarg(x_1722);
lean_dec(x_1722);
x_1724 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1723);
x_1725 = l_Array_HasRepr___rarg___closed__1;
x_1726 = lean_string_append(x_1725, x_1724);
lean_dec(x_1724);
x_1727 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1727, 0, x_1726);
x_1728 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1728, 0, x_1727);
x_1729 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1729, 0, x_1719);
lean_ctor_set(x_1729, 1, x_1728);
x_1730 = l_Lean_Elab_Term_throwError___rarg(x_1729, x_1456, x_1713);
return x_1730;
}
else
{
lean_object* x_1731; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; uint8_t x_1760; 
lean_dec(x_1530);
lean_dec(x_11);
x_1756 = l_Lean_Elab_Term_getOptions(x_1456, x_1713);
x_1757 = lean_ctor_get(x_1756, 0);
lean_inc(x_1757);
x_1758 = lean_ctor_get(x_1756, 1);
lean_inc(x_1758);
lean_dec(x_1756);
x_1759 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1760 = l_Lean_checkTraceOption(x_1757, x_1759);
lean_dec(x_1757);
if (x_1760 == 0)
{
x_1731 = x_1758;
goto block_1755;
}
else
{
lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; 
lean_inc(x_2);
x_1761 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1761, 0, x_2);
x_1762 = l_Lean_Elab_Term_logTrace(x_1759, x_1761, x_1456, x_1758);
x_1763 = lean_ctor_get(x_1762, 1);
lean_inc(x_1763);
lean_dec(x_1762);
x_1731 = x_1763;
goto block_1755;
}
block_1755:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1732; 
lean_dec(x_3);
x_1732 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_1731);
lean_dec(x_12);
if (lean_obj_tag(x_1732) == 0)
{
lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; 
x_1733 = lean_ctor_get(x_1732, 1);
lean_inc(x_1733);
if (lean_is_exclusive(x_1732)) {
 lean_ctor_release(x_1732, 0);
 lean_ctor_release(x_1732, 1);
 x_1734 = x_1732;
} else {
 lean_dec_ref(x_1732);
 x_1734 = lean_box(0);
}
if (lean_is_scalar(x_1734)) {
 x_1735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1735 = x_1734;
}
lean_ctor_set(x_1735, 0, x_2);
lean_ctor_set(x_1735, 1, x_1733);
return x_1735;
}
else
{
lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; 
lean_dec(x_2);
x_1736 = lean_ctor_get(x_1732, 0);
lean_inc(x_1736);
x_1737 = lean_ctor_get(x_1732, 1);
lean_inc(x_1737);
if (lean_is_exclusive(x_1732)) {
 lean_ctor_release(x_1732, 0);
 lean_ctor_release(x_1732, 1);
 x_1738 = x_1732;
} else {
 lean_dec_ref(x_1732);
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
else
{
lean_object* x_1740; lean_object* x_1741; 
x_1740 = lean_ctor_get(x_8, 0);
lean_inc(x_1740);
lean_dec(x_8);
lean_inc(x_1456);
x_1741 = l_Lean_Elab_Term_isDefEq(x_1740, x_3, x_1456, x_1731);
if (lean_obj_tag(x_1741) == 0)
{
lean_object* x_1742; lean_object* x_1743; 
x_1742 = lean_ctor_get(x_1741, 1);
lean_inc(x_1742);
lean_dec(x_1741);
x_1743 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_1742);
lean_dec(x_12);
if (lean_obj_tag(x_1743) == 0)
{
lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; 
x_1744 = lean_ctor_get(x_1743, 1);
lean_inc(x_1744);
if (lean_is_exclusive(x_1743)) {
 lean_ctor_release(x_1743, 0);
 lean_ctor_release(x_1743, 1);
 x_1745 = x_1743;
} else {
 lean_dec_ref(x_1743);
 x_1745 = lean_box(0);
}
if (lean_is_scalar(x_1745)) {
 x_1746 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1746 = x_1745;
}
lean_ctor_set(x_1746, 0, x_2);
lean_ctor_set(x_1746, 1, x_1744);
return x_1746;
}
else
{
lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; 
lean_dec(x_2);
x_1747 = lean_ctor_get(x_1743, 0);
lean_inc(x_1747);
x_1748 = lean_ctor_get(x_1743, 1);
lean_inc(x_1748);
if (lean_is_exclusive(x_1743)) {
 lean_ctor_release(x_1743, 0);
 lean_ctor_release(x_1743, 1);
 x_1749 = x_1743;
} else {
 lean_dec_ref(x_1743);
 x_1749 = lean_box(0);
}
if (lean_is_scalar(x_1749)) {
 x_1750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1750 = x_1749;
}
lean_ctor_set(x_1750, 0, x_1747);
lean_ctor_set(x_1750, 1, x_1748);
return x_1750;
}
}
else
{
lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; 
lean_dec(x_1456);
lean_dec(x_12);
lean_dec(x_2);
x_1751 = lean_ctor_get(x_1741, 0);
lean_inc(x_1751);
x_1752 = lean_ctor_get(x_1741, 1);
lean_inc(x_1752);
if (lean_is_exclusive(x_1741)) {
 lean_ctor_release(x_1741, 0);
 lean_ctor_release(x_1741, 1);
 x_1753 = x_1741;
} else {
 lean_dec_ref(x_1741);
 x_1753 = lean_box(0);
}
if (lean_is_scalar(x_1753)) {
 x_1754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1754 = x_1753;
}
lean_ctor_set(x_1754, 0, x_1751);
lean_ctor_set(x_1754, 1, x_1752);
return x_1754;
}
}
}
}
}
else
{
lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; 
lean_dec(x_1530);
lean_dec(x_3);
x_1764 = lean_ctor_get(x_1711, 1);
lean_inc(x_1764);
lean_dec(x_1711);
x_1765 = lean_array_fget(x_7, x_10);
lean_inc(x_1456);
lean_inc(x_2);
x_1766 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1765, x_1531, x_1456, x_1764);
if (lean_obj_tag(x_1766) == 0)
{
lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; uint8_t x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; 
x_1767 = lean_ctor_get(x_1766, 0);
lean_inc(x_1767);
x_1768 = lean_ctor_get(x_1766, 1);
lean_inc(x_1768);
lean_dec(x_1766);
x_1769 = lean_unsigned_to_nat(1u);
x_1770 = lean_nat_add(x_10, x_1769);
lean_dec(x_10);
x_1771 = 1;
if (lean_is_scalar(x_1712)) {
 x_1772 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1772 = x_1712;
}
lean_ctor_set(x_1772, 0, x_6);
lean_ctor_set(x_1772, 1, x_7);
lean_ctor_set(x_1772, 2, x_8);
lean_ctor_set(x_1772, 3, x_1770);
lean_ctor_set(x_1772, 4, x_11);
lean_ctor_set(x_1772, 5, x_12);
lean_ctor_set(x_1772, 6, x_13);
lean_ctor_set_uint8(x_1772, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1772, sizeof(void*)*7 + 1, x_1771);
lean_inc(x_1767);
x_1773 = l_Lean_mkApp(x_2, x_1767);
x_1774 = lean_expr_instantiate1(x_1532, x_1767);
lean_dec(x_1767);
lean_dec(x_1532);
x_1 = x_1772;
x_2 = x_1773;
x_3 = x_1774;
x_4 = x_1456;
x_5 = x_1768;
goto _start;
}
else
{
lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; 
lean_dec(x_1712);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1776 = lean_ctor_get(x_1766, 0);
lean_inc(x_1776);
x_1777 = lean_ctor_get(x_1766, 1);
lean_inc(x_1777);
if (lean_is_exclusive(x_1766)) {
 lean_ctor_release(x_1766, 0);
 lean_ctor_release(x_1766, 1);
 x_1778 = x_1766;
} else {
 lean_dec_ref(x_1766);
 x_1778 = lean_box(0);
}
if (lean_is_scalar(x_1778)) {
 x_1779 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1779 = x_1778;
}
lean_ctor_set(x_1779, 0, x_1776);
lean_ctor_set(x_1779, 1, x_1777);
return x_1779;
}
}
}
else
{
lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; 
lean_dec(x_1712);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_1530);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_1780 = lean_ctor_get(x_1711, 0);
lean_inc(x_1780);
x_1781 = lean_ctor_get(x_1711, 1);
lean_inc(x_1781);
if (lean_is_exclusive(x_1711)) {
 lean_ctor_release(x_1711, 0);
 lean_ctor_release(x_1711, 1);
 x_1782 = x_1711;
} else {
 lean_dec_ref(x_1711);
 x_1782 = lean_box(0);
}
if (lean_is_scalar(x_1782)) {
 x_1783 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1783 = x_1782;
}
lean_ctor_set(x_1783, 0, x_1780);
lean_ctor_set(x_1783, 1, x_1781);
return x_1783;
}
}
}
case 2:
{
uint8_t x_1784; lean_object* x_1785; lean_object* x_1786; uint8_t x_1787; lean_object* x_1788; lean_object* x_1789; 
x_1784 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1785 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1785, 0, x_6);
lean_ctor_set(x_1785, 1, x_7);
lean_ctor_set(x_1785, 2, x_8);
lean_ctor_set(x_1785, 3, x_10);
lean_ctor_set(x_1785, 4, x_11);
lean_ctor_set(x_1785, 5, x_12);
lean_ctor_set(x_1785, 6, x_13);
lean_ctor_set_uint8(x_1785, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1785, sizeof(void*)*7 + 1, x_1784);
x_1786 = lean_array_get_size(x_7);
x_1787 = lean_nat_dec_lt(x_10, x_1786);
lean_dec(x_1786);
lean_inc(x_1456);
lean_inc(x_1);
x_1788 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1458, x_1456, x_1459);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1789 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1789 = lean_box(0);
}
if (lean_obj_tag(x_1788) == 0)
{
lean_object* x_1790; lean_object* x_1791; 
x_1790 = lean_ctor_get(x_1788, 1);
lean_inc(x_1790);
lean_dec(x_1788);
if (x_1787 == 0)
{
lean_dec(x_1789);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1843; 
x_1843 = l_Lean_Expr_getOptParamDefault_x3f(x_1531);
if (lean_obj_tag(x_1843) == 0)
{
lean_object* x_1844; 
x_1844 = l_Lean_Expr_getAutoParamTactic_x3f(x_1531);
if (lean_obj_tag(x_1844) == 0)
{
lean_object* x_1845; 
lean_dec(x_1785);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
x_1845 = lean_box(0);
x_1791 = x_1845;
goto block_1842;
}
else
{
lean_object* x_1846; 
lean_dec(x_1530);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1846 = lean_ctor_get(x_1844, 0);
lean_inc(x_1846);
lean_dec(x_1844);
if (lean_obj_tag(x_1846) == 4)
{
lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; 
x_1847 = lean_ctor_get(x_1846, 0);
lean_inc(x_1847);
lean_dec(x_1846);
x_1848 = l_Lean_Elab_Term_getEnv___rarg(x_1790);
x_1849 = lean_ctor_get(x_1848, 0);
lean_inc(x_1849);
x_1850 = lean_ctor_get(x_1848, 1);
lean_inc(x_1850);
lean_dec(x_1848);
x_1851 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1849, x_1847);
if (lean_obj_tag(x_1851) == 0)
{
lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; 
lean_dec(x_1785);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
lean_dec(x_2);
x_1852 = lean_ctor_get(x_1851, 0);
lean_inc(x_1852);
lean_dec(x_1851);
x_1853 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1853, 0, x_1852);
x_1854 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1854, 0, x_1853);
x_1855 = l_Lean_Elab_Term_throwError___rarg(x_1854, x_1456, x_1850);
return x_1855;
}
else
{
lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; 
x_1856 = lean_ctor_get(x_1851, 0);
lean_inc(x_1856);
lean_dec(x_1851);
x_1857 = l_Lean_Elab_Term_getCurrMacroScope(x_1456, x_1850);
x_1858 = lean_ctor_get(x_1857, 1);
lean_inc(x_1858);
lean_dec(x_1857);
x_1859 = l_Lean_Elab_Term_getMainModule___rarg(x_1858);
x_1860 = lean_ctor_get(x_1859, 1);
lean_inc(x_1860);
lean_dec(x_1859);
x_1861 = l_Lean_Syntax_getArgs(x_1856);
lean_dec(x_1856);
x_1862 = l_Array_empty___closed__1;
x_1863 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1861, x_1861, x_1534, x_1862);
lean_dec(x_1861);
x_1864 = l_Lean_nullKind___closed__2;
x_1865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1865, 0, x_1864);
lean_ctor_set(x_1865, 1, x_1863);
x_1866 = lean_array_push(x_1862, x_1865);
x_1867 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_1868 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1868, 0, x_1867);
lean_ctor_set(x_1868, 1, x_1866);
x_1869 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1870 = lean_array_push(x_1869, x_1868);
x_1871 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1872 = lean_array_push(x_1870, x_1871);
x_1873 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1874 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1874, 0, x_1873);
lean_ctor_set(x_1874, 1, x_1872);
x_1875 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_1876 = l_Lean_Expr_getAppNumArgsAux___main(x_1531, x_1534);
x_1877 = lean_nat_sub(x_1876, x_1534);
lean_dec(x_1876);
x_1878 = lean_unsigned_to_nat(1u);
x_1879 = lean_nat_sub(x_1877, x_1878);
lean_dec(x_1877);
x_1880 = l_Lean_Expr_getRevArg_x21___main(x_1531, x_1879);
lean_dec(x_1531);
if (lean_obj_tag(x_1875) == 0)
{
lean_object* x_1881; lean_object* x_1882; 
x_1881 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1881, 0, x_1874);
lean_inc(x_1456);
lean_inc(x_2);
x_1882 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1881, x_1880, x_1456, x_1860);
if (lean_obj_tag(x_1882) == 0)
{
lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; 
x_1883 = lean_ctor_get(x_1882, 0);
lean_inc(x_1883);
x_1884 = lean_ctor_get(x_1882, 1);
lean_inc(x_1884);
lean_dec(x_1882);
lean_inc(x_1883);
x_1885 = l_Lean_mkApp(x_2, x_1883);
x_1886 = lean_expr_instantiate1(x_1532, x_1883);
lean_dec(x_1883);
lean_dec(x_1532);
x_1 = x_1785;
x_2 = x_1885;
x_3 = x_1886;
x_4 = x_1456;
x_5 = x_1884;
goto _start;
}
else
{
lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; 
lean_dec(x_1785);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_2);
x_1888 = lean_ctor_get(x_1882, 0);
lean_inc(x_1888);
x_1889 = lean_ctor_get(x_1882, 1);
lean_inc(x_1889);
if (lean_is_exclusive(x_1882)) {
 lean_ctor_release(x_1882, 0);
 lean_ctor_release(x_1882, 1);
 x_1890 = x_1882;
} else {
 lean_dec_ref(x_1882);
 x_1890 = lean_box(0);
}
if (lean_is_scalar(x_1890)) {
 x_1891 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1891 = x_1890;
}
lean_ctor_set(x_1891, 0, x_1888);
lean_ctor_set(x_1891, 1, x_1889);
return x_1891;
}
}
else
{
lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; 
x_1892 = lean_ctor_get(x_1875, 0);
lean_inc(x_1892);
lean_dec(x_1875);
x_1893 = l_Lean_Syntax_replaceInfo___main(x_1892, x_1874);
x_1894 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1894, 0, x_1893);
lean_inc(x_1456);
lean_inc(x_2);
x_1895 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1894, x_1880, x_1456, x_1860);
if (lean_obj_tag(x_1895) == 0)
{
lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; 
x_1896 = lean_ctor_get(x_1895, 0);
lean_inc(x_1896);
x_1897 = lean_ctor_get(x_1895, 1);
lean_inc(x_1897);
lean_dec(x_1895);
lean_inc(x_1896);
x_1898 = l_Lean_mkApp(x_2, x_1896);
x_1899 = lean_expr_instantiate1(x_1532, x_1896);
lean_dec(x_1896);
lean_dec(x_1532);
x_1 = x_1785;
x_2 = x_1898;
x_3 = x_1899;
x_4 = x_1456;
x_5 = x_1897;
goto _start;
}
else
{
lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; 
lean_dec(x_1785);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_2);
x_1901 = lean_ctor_get(x_1895, 0);
lean_inc(x_1901);
x_1902 = lean_ctor_get(x_1895, 1);
lean_inc(x_1902);
if (lean_is_exclusive(x_1895)) {
 lean_ctor_release(x_1895, 0);
 lean_ctor_release(x_1895, 1);
 x_1903 = x_1895;
} else {
 lean_dec_ref(x_1895);
 x_1903 = lean_box(0);
}
if (lean_is_scalar(x_1903)) {
 x_1904 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1904 = x_1903;
}
lean_ctor_set(x_1904, 0, x_1901);
lean_ctor_set(x_1904, 1, x_1902);
return x_1904;
}
}
}
}
else
{
lean_object* x_1905; lean_object* x_1906; 
lean_dec(x_1846);
lean_dec(x_1785);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
lean_dec(x_2);
x_1905 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1906 = l_Lean_Elab_Term_throwError___rarg(x_1905, x_1456, x_1790);
return x_1906;
}
}
}
else
{
lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; 
lean_dec(x_1531);
lean_dec(x_1530);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1907 = lean_ctor_get(x_1843, 0);
lean_inc(x_1907);
lean_dec(x_1843);
lean_inc(x_1907);
x_1908 = l_Lean_mkApp(x_2, x_1907);
x_1909 = lean_expr_instantiate1(x_1532, x_1907);
lean_dec(x_1907);
lean_dec(x_1532);
x_1 = x_1785;
x_2 = x_1908;
x_3 = x_1909;
x_4 = x_1456;
x_5 = x_1790;
goto _start;
}
}
else
{
lean_object* x_1911; 
lean_dec(x_1785);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
x_1911 = lean_box(0);
x_1791 = x_1911;
goto block_1842;
}
}
else
{
lean_object* x_1912; lean_object* x_1913; 
lean_dec(x_1785);
lean_dec(x_1530);
lean_dec(x_3);
x_1912 = lean_array_fget(x_7, x_10);
lean_inc(x_1456);
lean_inc(x_2);
x_1913 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1912, x_1531, x_1456, x_1790);
if (lean_obj_tag(x_1913) == 0)
{
lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; 
x_1914 = lean_ctor_get(x_1913, 0);
lean_inc(x_1914);
x_1915 = lean_ctor_get(x_1913, 1);
lean_inc(x_1915);
lean_dec(x_1913);
x_1916 = lean_unsigned_to_nat(1u);
x_1917 = lean_nat_add(x_10, x_1916);
lean_dec(x_10);
if (lean_is_scalar(x_1789)) {
 x_1918 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1918 = x_1789;
}
lean_ctor_set(x_1918, 0, x_6);
lean_ctor_set(x_1918, 1, x_7);
lean_ctor_set(x_1918, 2, x_8);
lean_ctor_set(x_1918, 3, x_1917);
lean_ctor_set(x_1918, 4, x_11);
lean_ctor_set(x_1918, 5, x_12);
lean_ctor_set(x_1918, 6, x_13);
lean_ctor_set_uint8(x_1918, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1918, sizeof(void*)*7 + 1, x_1784);
lean_inc(x_1914);
x_1919 = l_Lean_mkApp(x_2, x_1914);
x_1920 = lean_expr_instantiate1(x_1532, x_1914);
lean_dec(x_1914);
lean_dec(x_1532);
x_1 = x_1918;
x_2 = x_1919;
x_3 = x_1920;
x_4 = x_1456;
x_5 = x_1915;
goto _start;
}
else
{
lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; 
lean_dec(x_1789);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_1922 = lean_ctor_get(x_1913, 0);
lean_inc(x_1922);
x_1923 = lean_ctor_get(x_1913, 1);
lean_inc(x_1923);
if (lean_is_exclusive(x_1913)) {
 lean_ctor_release(x_1913, 0);
 lean_ctor_release(x_1913, 1);
 x_1924 = x_1913;
} else {
 lean_dec_ref(x_1913);
 x_1924 = lean_box(0);
}
if (lean_is_scalar(x_1924)) {
 x_1925 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1925 = x_1924;
}
lean_ctor_set(x_1925, 0, x_1922);
lean_ctor_set(x_1925, 1, x_1923);
return x_1925;
}
}
block_1842:
{
uint8_t x_1792; 
lean_dec(x_1791);
x_1792 = l_Array_isEmpty___rarg(x_11);
if (x_1792 == 0)
{
lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1793 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1793, 0, x_1530);
x_1794 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1795 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1795, 0, x_1794);
lean_ctor_set(x_1795, 1, x_1793);
x_1796 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1797 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1797, 0, x_1795);
lean_ctor_set(x_1797, 1, x_1796);
x_1798 = x_11;
x_1799 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1534, x_1798);
x_1800 = x_1799;
x_1801 = l_Array_toList___rarg(x_1800);
lean_dec(x_1800);
x_1802 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1801);
x_1803 = l_Array_HasRepr___rarg___closed__1;
x_1804 = lean_string_append(x_1803, x_1802);
lean_dec(x_1802);
x_1805 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1805, 0, x_1804);
x_1806 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1806, 0, x_1805);
x_1807 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1807, 0, x_1797);
lean_ctor_set(x_1807, 1, x_1806);
x_1808 = l_Lean_Elab_Term_throwError___rarg(x_1807, x_1456, x_1790);
return x_1808;
}
else
{
lean_object* x_1809; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; uint8_t x_1838; 
lean_dec(x_1530);
lean_dec(x_11);
x_1834 = l_Lean_Elab_Term_getOptions(x_1456, x_1790);
x_1835 = lean_ctor_get(x_1834, 0);
lean_inc(x_1835);
x_1836 = lean_ctor_get(x_1834, 1);
lean_inc(x_1836);
lean_dec(x_1834);
x_1837 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1838 = l_Lean_checkTraceOption(x_1835, x_1837);
lean_dec(x_1835);
if (x_1838 == 0)
{
x_1809 = x_1836;
goto block_1833;
}
else
{
lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; 
lean_inc(x_2);
x_1839 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1839, 0, x_2);
x_1840 = l_Lean_Elab_Term_logTrace(x_1837, x_1839, x_1456, x_1836);
x_1841 = lean_ctor_get(x_1840, 1);
lean_inc(x_1841);
lean_dec(x_1840);
x_1809 = x_1841;
goto block_1833;
}
block_1833:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1810; 
lean_dec(x_3);
x_1810 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_1809);
lean_dec(x_12);
if (lean_obj_tag(x_1810) == 0)
{
lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; 
x_1811 = lean_ctor_get(x_1810, 1);
lean_inc(x_1811);
if (lean_is_exclusive(x_1810)) {
 lean_ctor_release(x_1810, 0);
 lean_ctor_release(x_1810, 1);
 x_1812 = x_1810;
} else {
 lean_dec_ref(x_1810);
 x_1812 = lean_box(0);
}
if (lean_is_scalar(x_1812)) {
 x_1813 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1813 = x_1812;
}
lean_ctor_set(x_1813, 0, x_2);
lean_ctor_set(x_1813, 1, x_1811);
return x_1813;
}
else
{
lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; 
lean_dec(x_2);
x_1814 = lean_ctor_get(x_1810, 0);
lean_inc(x_1814);
x_1815 = lean_ctor_get(x_1810, 1);
lean_inc(x_1815);
if (lean_is_exclusive(x_1810)) {
 lean_ctor_release(x_1810, 0);
 lean_ctor_release(x_1810, 1);
 x_1816 = x_1810;
} else {
 lean_dec_ref(x_1810);
 x_1816 = lean_box(0);
}
if (lean_is_scalar(x_1816)) {
 x_1817 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1817 = x_1816;
}
lean_ctor_set(x_1817, 0, x_1814);
lean_ctor_set(x_1817, 1, x_1815);
return x_1817;
}
}
else
{
lean_object* x_1818; lean_object* x_1819; 
x_1818 = lean_ctor_get(x_8, 0);
lean_inc(x_1818);
lean_dec(x_8);
lean_inc(x_1456);
x_1819 = l_Lean_Elab_Term_isDefEq(x_1818, x_3, x_1456, x_1809);
if (lean_obj_tag(x_1819) == 0)
{
lean_object* x_1820; lean_object* x_1821; 
x_1820 = lean_ctor_get(x_1819, 1);
lean_inc(x_1820);
lean_dec(x_1819);
x_1821 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_1820);
lean_dec(x_12);
if (lean_obj_tag(x_1821) == 0)
{
lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; 
x_1822 = lean_ctor_get(x_1821, 1);
lean_inc(x_1822);
if (lean_is_exclusive(x_1821)) {
 lean_ctor_release(x_1821, 0);
 lean_ctor_release(x_1821, 1);
 x_1823 = x_1821;
} else {
 lean_dec_ref(x_1821);
 x_1823 = lean_box(0);
}
if (lean_is_scalar(x_1823)) {
 x_1824 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1824 = x_1823;
}
lean_ctor_set(x_1824, 0, x_2);
lean_ctor_set(x_1824, 1, x_1822);
return x_1824;
}
else
{
lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; 
lean_dec(x_2);
x_1825 = lean_ctor_get(x_1821, 0);
lean_inc(x_1825);
x_1826 = lean_ctor_get(x_1821, 1);
lean_inc(x_1826);
if (lean_is_exclusive(x_1821)) {
 lean_ctor_release(x_1821, 0);
 lean_ctor_release(x_1821, 1);
 x_1827 = x_1821;
} else {
 lean_dec_ref(x_1821);
 x_1827 = lean_box(0);
}
if (lean_is_scalar(x_1827)) {
 x_1828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1828 = x_1827;
}
lean_ctor_set(x_1828, 0, x_1825);
lean_ctor_set(x_1828, 1, x_1826);
return x_1828;
}
}
else
{
lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; 
lean_dec(x_1456);
lean_dec(x_12);
lean_dec(x_2);
x_1829 = lean_ctor_get(x_1819, 0);
lean_inc(x_1829);
x_1830 = lean_ctor_get(x_1819, 1);
lean_inc(x_1830);
if (lean_is_exclusive(x_1819)) {
 lean_ctor_release(x_1819, 0);
 lean_ctor_release(x_1819, 1);
 x_1831 = x_1819;
} else {
 lean_dec_ref(x_1819);
 x_1831 = lean_box(0);
}
if (lean_is_scalar(x_1831)) {
 x_1832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1832 = x_1831;
}
lean_ctor_set(x_1832, 0, x_1829);
lean_ctor_set(x_1832, 1, x_1830);
return x_1832;
}
}
}
}
}
}
else
{
lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; 
lean_dec(x_1789);
lean_dec(x_1785);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_1530);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_1926 = lean_ctor_get(x_1788, 0);
lean_inc(x_1926);
x_1927 = lean_ctor_get(x_1788, 1);
lean_inc(x_1927);
if (lean_is_exclusive(x_1788)) {
 lean_ctor_release(x_1788, 0);
 lean_ctor_release(x_1788, 1);
 x_1928 = x_1788;
} else {
 lean_dec_ref(x_1788);
 x_1928 = lean_box(0);
}
if (lean_is_scalar(x_1928)) {
 x_1929 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1929 = x_1928;
}
lean_ctor_set(x_1929, 0, x_1926);
lean_ctor_set(x_1929, 1, x_1927);
return x_1929;
}
}
case 3:
{
if (x_9 == 0)
{
lean_object* x_1930; lean_object* x_1931; uint8_t x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; 
lean_dec(x_1530);
lean_dec(x_1458);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1930 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1930 = lean_box(0);
}
x_1931 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1931, 0, x_1531);
x_1932 = 1;
x_1933 = lean_box(0);
lean_inc(x_1456);
x_1934 = l_Lean_Elab_Term_mkFreshExprMVar(x_1931, x_1932, x_1933, x_1456, x_1459);
x_1935 = lean_ctor_get(x_1934, 0);
lean_inc(x_1935);
x_1936 = lean_ctor_get(x_1934, 1);
lean_inc(x_1936);
lean_dec(x_1934);
x_1937 = l_Lean_Expr_mvarId_x21(x_1935);
x_1938 = lean_array_push(x_12, x_1937);
if (lean_is_scalar(x_1930)) {
 x_1939 = lean_alloc_ctor(0, 7, 2);
} else {
 x_1939 = x_1930;
}
lean_ctor_set(x_1939, 0, x_6);
lean_ctor_set(x_1939, 1, x_7);
lean_ctor_set(x_1939, 2, x_8);
lean_ctor_set(x_1939, 3, x_10);
lean_ctor_set(x_1939, 4, x_11);
lean_ctor_set(x_1939, 5, x_1938);
lean_ctor_set(x_1939, 6, x_13);
lean_ctor_set_uint8(x_1939, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1939, sizeof(void*)*7 + 1, x_1441);
lean_inc(x_1935);
x_1940 = l_Lean_mkApp(x_2, x_1935);
x_1941 = lean_expr_instantiate1(x_1532, x_1935);
lean_dec(x_1935);
lean_dec(x_1532);
x_1 = x_1939;
x_2 = x_1940;
x_3 = x_1941;
x_4 = x_1456;
x_5 = x_1936;
goto _start;
}
else
{
uint8_t x_1943; 
x_1943 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_1943 == 0)
{
lean_object* x_1944; uint8_t x_1945; lean_object* x_1946; lean_object* x_1947; 
x_1944 = lean_array_get_size(x_7);
x_1945 = lean_nat_dec_lt(x_10, x_1944);
lean_dec(x_1944);
lean_inc(x_1456);
lean_inc(x_1);
x_1946 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1458, x_1456, x_1459);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_1947 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1947 = lean_box(0);
}
if (lean_obj_tag(x_1946) == 0)
{
if (x_1945 == 0)
{
lean_object* x_1948; uint8_t x_1949; 
lean_dec(x_1947);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_1948 = lean_ctor_get(x_1946, 1);
lean_inc(x_1948);
lean_dec(x_1946);
x_1949 = l_Array_isEmpty___rarg(x_11);
if (x_1949 == 0)
{
lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1950 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1950, 0, x_1530);
x_1951 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1952 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1952, 0, x_1951);
lean_ctor_set(x_1952, 1, x_1950);
x_1953 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1954 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1954, 0, x_1952);
lean_ctor_set(x_1954, 1, x_1953);
x_1955 = x_11;
x_1956 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1534, x_1955);
x_1957 = x_1956;
x_1958 = l_Array_toList___rarg(x_1957);
lean_dec(x_1957);
x_1959 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1958);
x_1960 = l_Array_HasRepr___rarg___closed__1;
x_1961 = lean_string_append(x_1960, x_1959);
lean_dec(x_1959);
x_1962 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1962, 0, x_1961);
x_1963 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1963, 0, x_1962);
x_1964 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1964, 0, x_1954);
lean_ctor_set(x_1964, 1, x_1963);
x_1965 = l_Lean_Elab_Term_throwError___rarg(x_1964, x_1456, x_1948);
return x_1965;
}
else
{
lean_object* x_1966; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; uint8_t x_1995; 
lean_dec(x_1530);
lean_dec(x_11);
x_1991 = l_Lean_Elab_Term_getOptions(x_1456, x_1948);
x_1992 = lean_ctor_get(x_1991, 0);
lean_inc(x_1992);
x_1993 = lean_ctor_get(x_1991, 1);
lean_inc(x_1993);
lean_dec(x_1991);
x_1994 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1995 = l_Lean_checkTraceOption(x_1992, x_1994);
lean_dec(x_1992);
if (x_1995 == 0)
{
x_1966 = x_1993;
goto block_1990;
}
else
{
lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; 
lean_inc(x_2);
x_1996 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1996, 0, x_2);
x_1997 = l_Lean_Elab_Term_logTrace(x_1994, x_1996, x_1456, x_1993);
x_1998 = lean_ctor_get(x_1997, 1);
lean_inc(x_1998);
lean_dec(x_1997);
x_1966 = x_1998;
goto block_1990;
}
block_1990:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1967; 
lean_dec(x_3);
x_1967 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_1966);
lean_dec(x_12);
if (lean_obj_tag(x_1967) == 0)
{
lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; 
x_1968 = lean_ctor_get(x_1967, 1);
lean_inc(x_1968);
if (lean_is_exclusive(x_1967)) {
 lean_ctor_release(x_1967, 0);
 lean_ctor_release(x_1967, 1);
 x_1969 = x_1967;
} else {
 lean_dec_ref(x_1967);
 x_1969 = lean_box(0);
}
if (lean_is_scalar(x_1969)) {
 x_1970 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1970 = x_1969;
}
lean_ctor_set(x_1970, 0, x_2);
lean_ctor_set(x_1970, 1, x_1968);
return x_1970;
}
else
{
lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; 
lean_dec(x_2);
x_1971 = lean_ctor_get(x_1967, 0);
lean_inc(x_1971);
x_1972 = lean_ctor_get(x_1967, 1);
lean_inc(x_1972);
if (lean_is_exclusive(x_1967)) {
 lean_ctor_release(x_1967, 0);
 lean_ctor_release(x_1967, 1);
 x_1973 = x_1967;
} else {
 lean_dec_ref(x_1967);
 x_1973 = lean_box(0);
}
if (lean_is_scalar(x_1973)) {
 x_1974 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1974 = x_1973;
}
lean_ctor_set(x_1974, 0, x_1971);
lean_ctor_set(x_1974, 1, x_1972);
return x_1974;
}
}
else
{
lean_object* x_1975; lean_object* x_1976; 
x_1975 = lean_ctor_get(x_8, 0);
lean_inc(x_1975);
lean_dec(x_8);
lean_inc(x_1456);
x_1976 = l_Lean_Elab_Term_isDefEq(x_1975, x_3, x_1456, x_1966);
if (lean_obj_tag(x_1976) == 0)
{
lean_object* x_1977; lean_object* x_1978; 
x_1977 = lean_ctor_get(x_1976, 1);
lean_inc(x_1977);
lean_dec(x_1976);
x_1978 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_1977);
lean_dec(x_12);
if (lean_obj_tag(x_1978) == 0)
{
lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; 
x_1979 = lean_ctor_get(x_1978, 1);
lean_inc(x_1979);
if (lean_is_exclusive(x_1978)) {
 lean_ctor_release(x_1978, 0);
 lean_ctor_release(x_1978, 1);
 x_1980 = x_1978;
} else {
 lean_dec_ref(x_1978);
 x_1980 = lean_box(0);
}
if (lean_is_scalar(x_1980)) {
 x_1981 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1981 = x_1980;
}
lean_ctor_set(x_1981, 0, x_2);
lean_ctor_set(x_1981, 1, x_1979);
return x_1981;
}
else
{
lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; 
lean_dec(x_2);
x_1982 = lean_ctor_get(x_1978, 0);
lean_inc(x_1982);
x_1983 = lean_ctor_get(x_1978, 1);
lean_inc(x_1983);
if (lean_is_exclusive(x_1978)) {
 lean_ctor_release(x_1978, 0);
 lean_ctor_release(x_1978, 1);
 x_1984 = x_1978;
} else {
 lean_dec_ref(x_1978);
 x_1984 = lean_box(0);
}
if (lean_is_scalar(x_1984)) {
 x_1985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1985 = x_1984;
}
lean_ctor_set(x_1985, 0, x_1982);
lean_ctor_set(x_1985, 1, x_1983);
return x_1985;
}
}
else
{
lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; 
lean_dec(x_1456);
lean_dec(x_12);
lean_dec(x_2);
x_1986 = lean_ctor_get(x_1976, 0);
lean_inc(x_1986);
x_1987 = lean_ctor_get(x_1976, 1);
lean_inc(x_1987);
if (lean_is_exclusive(x_1976)) {
 lean_ctor_release(x_1976, 0);
 lean_ctor_release(x_1976, 1);
 x_1988 = x_1976;
} else {
 lean_dec_ref(x_1976);
 x_1988 = lean_box(0);
}
if (lean_is_scalar(x_1988)) {
 x_1989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1989 = x_1988;
}
lean_ctor_set(x_1989, 0, x_1986);
lean_ctor_set(x_1989, 1, x_1987);
return x_1989;
}
}
}
}
}
else
{
lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; 
lean_dec(x_1530);
lean_dec(x_3);
x_1999 = lean_ctor_get(x_1946, 1);
lean_inc(x_1999);
lean_dec(x_1946);
x_2000 = lean_array_fget(x_7, x_10);
lean_inc(x_1456);
lean_inc(x_2);
x_2001 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2000, x_1531, x_1456, x_1999);
if (lean_obj_tag(x_2001) == 0)
{
lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; uint8_t x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; 
x_2002 = lean_ctor_get(x_2001, 0);
lean_inc(x_2002);
x_2003 = lean_ctor_get(x_2001, 1);
lean_inc(x_2003);
lean_dec(x_2001);
x_2004 = lean_unsigned_to_nat(1u);
x_2005 = lean_nat_add(x_10, x_2004);
lean_dec(x_10);
x_2006 = 1;
if (lean_is_scalar(x_1947)) {
 x_2007 = lean_alloc_ctor(0, 7, 2);
} else {
 x_2007 = x_1947;
}
lean_ctor_set(x_2007, 0, x_6);
lean_ctor_set(x_2007, 1, x_7);
lean_ctor_set(x_2007, 2, x_8);
lean_ctor_set(x_2007, 3, x_2005);
lean_ctor_set(x_2007, 4, x_11);
lean_ctor_set(x_2007, 5, x_12);
lean_ctor_set(x_2007, 6, x_13);
lean_ctor_set_uint8(x_2007, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2007, sizeof(void*)*7 + 1, x_2006);
lean_inc(x_2002);
x_2008 = l_Lean_mkApp(x_2, x_2002);
x_2009 = lean_expr_instantiate1(x_1532, x_2002);
lean_dec(x_2002);
lean_dec(x_1532);
x_1 = x_2007;
x_2 = x_2008;
x_3 = x_2009;
x_4 = x_1456;
x_5 = x_2003;
goto _start;
}
else
{
lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; 
lean_dec(x_1947);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_2011 = lean_ctor_get(x_2001, 0);
lean_inc(x_2011);
x_2012 = lean_ctor_get(x_2001, 1);
lean_inc(x_2012);
if (lean_is_exclusive(x_2001)) {
 lean_ctor_release(x_2001, 0);
 lean_ctor_release(x_2001, 1);
 x_2013 = x_2001;
} else {
 lean_dec_ref(x_2001);
 x_2013 = lean_box(0);
}
if (lean_is_scalar(x_2013)) {
 x_2014 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2014 = x_2013;
}
lean_ctor_set(x_2014, 0, x_2011);
lean_ctor_set(x_2014, 1, x_2012);
return x_2014;
}
}
}
else
{
lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; 
lean_dec(x_1947);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_1530);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_2015 = lean_ctor_get(x_1946, 0);
lean_inc(x_2015);
x_2016 = lean_ctor_get(x_1946, 1);
lean_inc(x_2016);
if (lean_is_exclusive(x_1946)) {
 lean_ctor_release(x_1946, 0);
 lean_ctor_release(x_1946, 1);
 x_2017 = x_1946;
} else {
 lean_dec_ref(x_1946);
 x_2017 = lean_box(0);
}
if (lean_is_scalar(x_2017)) {
 x_2018 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2018 = x_2017;
}
lean_ctor_set(x_2018, 0, x_2015);
lean_ctor_set(x_2018, 1, x_2016);
return x_2018;
}
}
else
{
lean_object* x_2019; lean_object* x_2020; uint8_t x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; 
lean_dec(x_1530);
lean_dec(x_1458);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_2019 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2019 = lean_box(0);
}
x_2020 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2020, 0, x_1531);
x_2021 = 1;
x_2022 = lean_box(0);
lean_inc(x_1456);
x_2023 = l_Lean_Elab_Term_mkFreshExprMVar(x_2020, x_2021, x_2022, x_1456, x_1459);
x_2024 = lean_ctor_get(x_2023, 0);
lean_inc(x_2024);
x_2025 = lean_ctor_get(x_2023, 1);
lean_inc(x_2025);
lean_dec(x_2023);
x_2026 = lean_unsigned_to_nat(1u);
x_2027 = lean_nat_add(x_10, x_2026);
lean_dec(x_10);
x_2028 = l_Lean_Expr_mvarId_x21(x_2024);
x_2029 = lean_array_push(x_12, x_2028);
if (lean_is_scalar(x_2019)) {
 x_2030 = lean_alloc_ctor(0, 7, 2);
} else {
 x_2030 = x_2019;
}
lean_ctor_set(x_2030, 0, x_6);
lean_ctor_set(x_2030, 1, x_7);
lean_ctor_set(x_2030, 2, x_8);
lean_ctor_set(x_2030, 3, x_2027);
lean_ctor_set(x_2030, 4, x_11);
lean_ctor_set(x_2030, 5, x_2029);
lean_ctor_set(x_2030, 6, x_13);
lean_ctor_set_uint8(x_2030, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2030, sizeof(void*)*7 + 1, x_1441);
lean_inc(x_2024);
x_2031 = l_Lean_mkApp(x_2, x_2024);
x_2032 = lean_expr_instantiate1(x_1532, x_2024);
lean_dec(x_2024);
lean_dec(x_1532);
x_1 = x_2030;
x_2 = x_2031;
x_3 = x_2032;
x_4 = x_1456;
x_5 = x_2025;
goto _start;
}
}
}
default: 
{
uint8_t x_2034; lean_object* x_2035; lean_object* x_2036; uint8_t x_2037; lean_object* x_2038; lean_object* x_2039; 
x_2034 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2035 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_2035, 0, x_6);
lean_ctor_set(x_2035, 1, x_7);
lean_ctor_set(x_2035, 2, x_8);
lean_ctor_set(x_2035, 3, x_10);
lean_ctor_set(x_2035, 4, x_11);
lean_ctor_set(x_2035, 5, x_12);
lean_ctor_set(x_2035, 6, x_13);
lean_ctor_set_uint8(x_2035, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2035, sizeof(void*)*7 + 1, x_2034);
x_2036 = lean_array_get_size(x_7);
x_2037 = lean_nat_dec_lt(x_10, x_2036);
lean_dec(x_2036);
lean_inc(x_1456);
lean_inc(x_1);
x_2038 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1458, x_1456, x_1459);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 x_2039 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2039 = lean_box(0);
}
if (lean_obj_tag(x_2038) == 0)
{
lean_object* x_2040; lean_object* x_2041; 
x_2040 = lean_ctor_get(x_2038, 1);
lean_inc(x_2040);
lean_dec(x_2038);
if (x_2037 == 0)
{
lean_dec(x_2039);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_2093; 
x_2093 = l_Lean_Expr_getOptParamDefault_x3f(x_1531);
if (lean_obj_tag(x_2093) == 0)
{
lean_object* x_2094; 
x_2094 = l_Lean_Expr_getAutoParamTactic_x3f(x_1531);
if (lean_obj_tag(x_2094) == 0)
{
lean_object* x_2095; 
lean_dec(x_2035);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
x_2095 = lean_box(0);
x_2041 = x_2095;
goto block_2092;
}
else
{
lean_object* x_2096; 
lean_dec(x_1530);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_2096 = lean_ctor_get(x_2094, 0);
lean_inc(x_2096);
lean_dec(x_2094);
if (lean_obj_tag(x_2096) == 4)
{
lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; 
x_2097 = lean_ctor_get(x_2096, 0);
lean_inc(x_2097);
lean_dec(x_2096);
x_2098 = l_Lean_Elab_Term_getEnv___rarg(x_2040);
x_2099 = lean_ctor_get(x_2098, 0);
lean_inc(x_2099);
x_2100 = lean_ctor_get(x_2098, 1);
lean_inc(x_2100);
lean_dec(x_2098);
x_2101 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_2099, x_2097);
if (lean_obj_tag(x_2101) == 0)
{
lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; 
lean_dec(x_2035);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
lean_dec(x_2);
x_2102 = lean_ctor_get(x_2101, 0);
lean_inc(x_2102);
lean_dec(x_2101);
x_2103 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2103, 0, x_2102);
x_2104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2104, 0, x_2103);
x_2105 = l_Lean_Elab_Term_throwError___rarg(x_2104, x_1456, x_2100);
return x_2105;
}
else
{
lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; lean_object* x_2130; 
x_2106 = lean_ctor_get(x_2101, 0);
lean_inc(x_2106);
lean_dec(x_2101);
x_2107 = l_Lean_Elab_Term_getCurrMacroScope(x_1456, x_2100);
x_2108 = lean_ctor_get(x_2107, 1);
lean_inc(x_2108);
lean_dec(x_2107);
x_2109 = l_Lean_Elab_Term_getMainModule___rarg(x_2108);
x_2110 = lean_ctor_get(x_2109, 1);
lean_inc(x_2110);
lean_dec(x_2109);
x_2111 = l_Lean_Syntax_getArgs(x_2106);
lean_dec(x_2106);
x_2112 = l_Array_empty___closed__1;
x_2113 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2111, x_2111, x_1534, x_2112);
lean_dec(x_2111);
x_2114 = l_Lean_nullKind___closed__2;
x_2115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2115, 0, x_2114);
lean_ctor_set(x_2115, 1, x_2113);
x_2116 = lean_array_push(x_2112, x_2115);
x_2117 = l_Lean_PrettyPrinter_Parenthesizer_tacticParser_parenthesizer___lambda__1___closed__4;
x_2118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2118, 0, x_2117);
lean_ctor_set(x_2118, 1, x_2116);
x_2119 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_2120 = lean_array_push(x_2119, x_2118);
x_2121 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_2122 = lean_array_push(x_2120, x_2121);
x_2123 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_2124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2124, 0, x_2123);
lean_ctor_set(x_2124, 1, x_2122);
x_2125 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean_dec(x_6);
x_2126 = l_Lean_Expr_getAppNumArgsAux___main(x_1531, x_1534);
x_2127 = lean_nat_sub(x_2126, x_1534);
lean_dec(x_2126);
x_2128 = lean_unsigned_to_nat(1u);
x_2129 = lean_nat_sub(x_2127, x_2128);
lean_dec(x_2127);
x_2130 = l_Lean_Expr_getRevArg_x21___main(x_1531, x_2129);
lean_dec(x_1531);
if (lean_obj_tag(x_2125) == 0)
{
lean_object* x_2131; lean_object* x_2132; 
x_2131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2131, 0, x_2124);
lean_inc(x_1456);
lean_inc(x_2);
x_2132 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2131, x_2130, x_1456, x_2110);
if (lean_obj_tag(x_2132) == 0)
{
lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; 
x_2133 = lean_ctor_get(x_2132, 0);
lean_inc(x_2133);
x_2134 = lean_ctor_get(x_2132, 1);
lean_inc(x_2134);
lean_dec(x_2132);
lean_inc(x_2133);
x_2135 = l_Lean_mkApp(x_2, x_2133);
x_2136 = lean_expr_instantiate1(x_1532, x_2133);
lean_dec(x_2133);
lean_dec(x_1532);
x_1 = x_2035;
x_2 = x_2135;
x_3 = x_2136;
x_4 = x_1456;
x_5 = x_2134;
goto _start;
}
else
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; 
lean_dec(x_2035);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_2);
x_2138 = lean_ctor_get(x_2132, 0);
lean_inc(x_2138);
x_2139 = lean_ctor_get(x_2132, 1);
lean_inc(x_2139);
if (lean_is_exclusive(x_2132)) {
 lean_ctor_release(x_2132, 0);
 lean_ctor_release(x_2132, 1);
 x_2140 = x_2132;
} else {
 lean_dec_ref(x_2132);
 x_2140 = lean_box(0);
}
if (lean_is_scalar(x_2140)) {
 x_2141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2141 = x_2140;
}
lean_ctor_set(x_2141, 0, x_2138);
lean_ctor_set(x_2141, 1, x_2139);
return x_2141;
}
}
else
{
lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; 
x_2142 = lean_ctor_get(x_2125, 0);
lean_inc(x_2142);
lean_dec(x_2125);
x_2143 = l_Lean_Syntax_replaceInfo___main(x_2142, x_2124);
x_2144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2144, 0, x_2143);
lean_inc(x_1456);
lean_inc(x_2);
x_2145 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2144, x_2130, x_1456, x_2110);
if (lean_obj_tag(x_2145) == 0)
{
lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; 
x_2146 = lean_ctor_get(x_2145, 0);
lean_inc(x_2146);
x_2147 = lean_ctor_get(x_2145, 1);
lean_inc(x_2147);
lean_dec(x_2145);
lean_inc(x_2146);
x_2148 = l_Lean_mkApp(x_2, x_2146);
x_2149 = lean_expr_instantiate1(x_1532, x_2146);
lean_dec(x_2146);
lean_dec(x_1532);
x_1 = x_2035;
x_2 = x_2148;
x_3 = x_2149;
x_4 = x_1456;
x_5 = x_2147;
goto _start;
}
else
{
lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; 
lean_dec(x_2035);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_2);
x_2151 = lean_ctor_get(x_2145, 0);
lean_inc(x_2151);
x_2152 = lean_ctor_get(x_2145, 1);
lean_inc(x_2152);
if (lean_is_exclusive(x_2145)) {
 lean_ctor_release(x_2145, 0);
 lean_ctor_release(x_2145, 1);
 x_2153 = x_2145;
} else {
 lean_dec_ref(x_2145);
 x_2153 = lean_box(0);
}
if (lean_is_scalar(x_2153)) {
 x_2154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2154 = x_2153;
}
lean_ctor_set(x_2154, 0, x_2151);
lean_ctor_set(x_2154, 1, x_2152);
return x_2154;
}
}
}
}
else
{
lean_object* x_2155; lean_object* x_2156; 
lean_dec(x_2096);
lean_dec(x_2035);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
lean_dec(x_2);
x_2155 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_2156 = l_Lean_Elab_Term_throwError___rarg(x_2155, x_1456, x_2040);
return x_2156;
}
}
}
else
{
lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; 
lean_dec(x_1531);
lean_dec(x_1530);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_2157 = lean_ctor_get(x_2093, 0);
lean_inc(x_2157);
lean_dec(x_2093);
lean_inc(x_2157);
x_2158 = l_Lean_mkApp(x_2, x_2157);
x_2159 = lean_expr_instantiate1(x_1532, x_2157);
lean_dec(x_2157);
lean_dec(x_1532);
x_1 = x_2035;
x_2 = x_2158;
x_3 = x_2159;
x_4 = x_1456;
x_5 = x_2040;
goto _start;
}
}
else
{
lean_object* x_2161; 
lean_dec(x_2035);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_6);
x_2161 = lean_box(0);
x_2041 = x_2161;
goto block_2092;
}
}
else
{
lean_object* x_2162; lean_object* x_2163; 
lean_dec(x_2035);
lean_dec(x_1530);
lean_dec(x_3);
x_2162 = lean_array_fget(x_7, x_10);
lean_inc(x_1456);
lean_inc(x_2);
x_2163 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2162, x_1531, x_1456, x_2040);
if (lean_obj_tag(x_2163) == 0)
{
lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; 
x_2164 = lean_ctor_get(x_2163, 0);
lean_inc(x_2164);
x_2165 = lean_ctor_get(x_2163, 1);
lean_inc(x_2165);
lean_dec(x_2163);
x_2166 = lean_unsigned_to_nat(1u);
x_2167 = lean_nat_add(x_10, x_2166);
lean_dec(x_10);
if (lean_is_scalar(x_2039)) {
 x_2168 = lean_alloc_ctor(0, 7, 2);
} else {
 x_2168 = x_2039;
}
lean_ctor_set(x_2168, 0, x_6);
lean_ctor_set(x_2168, 1, x_7);
lean_ctor_set(x_2168, 2, x_8);
lean_ctor_set(x_2168, 3, x_2167);
lean_ctor_set(x_2168, 4, x_11);
lean_ctor_set(x_2168, 5, x_12);
lean_ctor_set(x_2168, 6, x_13);
lean_ctor_set_uint8(x_2168, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2168, sizeof(void*)*7 + 1, x_2034);
lean_inc(x_2164);
x_2169 = l_Lean_mkApp(x_2, x_2164);
x_2170 = lean_expr_instantiate1(x_1532, x_2164);
lean_dec(x_2164);
lean_dec(x_1532);
x_1 = x_2168;
x_2 = x_2169;
x_3 = x_2170;
x_4 = x_1456;
x_5 = x_2165;
goto _start;
}
else
{
lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; 
lean_dec(x_2039);
lean_dec(x_1532);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_2172 = lean_ctor_get(x_2163, 0);
lean_inc(x_2172);
x_2173 = lean_ctor_get(x_2163, 1);
lean_inc(x_2173);
if (lean_is_exclusive(x_2163)) {
 lean_ctor_release(x_2163, 0);
 lean_ctor_release(x_2163, 1);
 x_2174 = x_2163;
} else {
 lean_dec_ref(x_2163);
 x_2174 = lean_box(0);
}
if (lean_is_scalar(x_2174)) {
 x_2175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2175 = x_2174;
}
lean_ctor_set(x_2175, 0, x_2172);
lean_ctor_set(x_2175, 1, x_2173);
return x_2175;
}
}
block_2092:
{
uint8_t x_2042; 
lean_dec(x_2041);
x_2042 = l_Array_isEmpty___rarg(x_11);
if (x_2042 == 0)
{
lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_2043 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2043, 0, x_1530);
x_2044 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2045 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2045, 0, x_2044);
lean_ctor_set(x_2045, 1, x_2043);
x_2046 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2047 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2047, 0, x_2045);
lean_ctor_set(x_2047, 1, x_2046);
x_2048 = x_11;
x_2049 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1534, x_2048);
x_2050 = x_2049;
x_2051 = l_Array_toList___rarg(x_2050);
lean_dec(x_2050);
x_2052 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2051);
x_2053 = l_Array_HasRepr___rarg___closed__1;
x_2054 = lean_string_append(x_2053, x_2052);
lean_dec(x_2052);
x_2055 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2055, 0, x_2054);
x_2056 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2056, 0, x_2055);
x_2057 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2057, 0, x_2047);
lean_ctor_set(x_2057, 1, x_2056);
x_2058 = l_Lean_Elab_Term_throwError___rarg(x_2057, x_1456, x_2040);
return x_2058;
}
else
{
lean_object* x_2059; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; uint8_t x_2088; 
lean_dec(x_1530);
lean_dec(x_11);
x_2084 = l_Lean_Elab_Term_getOptions(x_1456, x_2040);
x_2085 = lean_ctor_get(x_2084, 0);
lean_inc(x_2085);
x_2086 = lean_ctor_get(x_2084, 1);
lean_inc(x_2086);
lean_dec(x_2084);
x_2087 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2088 = l_Lean_checkTraceOption(x_2085, x_2087);
lean_dec(x_2085);
if (x_2088 == 0)
{
x_2059 = x_2086;
goto block_2083;
}
else
{
lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; 
lean_inc(x_2);
x_2089 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2089, 0, x_2);
x_2090 = l_Lean_Elab_Term_logTrace(x_2087, x_2089, x_1456, x_2086);
x_2091 = lean_ctor_get(x_2090, 1);
lean_inc(x_2091);
lean_dec(x_2090);
x_2059 = x_2091;
goto block_2083;
}
block_2083:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_2060; 
lean_dec(x_3);
x_2060 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_2059);
lean_dec(x_12);
if (lean_obj_tag(x_2060) == 0)
{
lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; 
x_2061 = lean_ctor_get(x_2060, 1);
lean_inc(x_2061);
if (lean_is_exclusive(x_2060)) {
 lean_ctor_release(x_2060, 0);
 lean_ctor_release(x_2060, 1);
 x_2062 = x_2060;
} else {
 lean_dec_ref(x_2060);
 x_2062 = lean_box(0);
}
if (lean_is_scalar(x_2062)) {
 x_2063 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2063 = x_2062;
}
lean_ctor_set(x_2063, 0, x_2);
lean_ctor_set(x_2063, 1, x_2061);
return x_2063;
}
else
{
lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; 
lean_dec(x_2);
x_2064 = lean_ctor_get(x_2060, 0);
lean_inc(x_2064);
x_2065 = lean_ctor_get(x_2060, 1);
lean_inc(x_2065);
if (lean_is_exclusive(x_2060)) {
 lean_ctor_release(x_2060, 0);
 lean_ctor_release(x_2060, 1);
 x_2066 = x_2060;
} else {
 lean_dec_ref(x_2060);
 x_2066 = lean_box(0);
}
if (lean_is_scalar(x_2066)) {
 x_2067 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2067 = x_2066;
}
lean_ctor_set(x_2067, 0, x_2064);
lean_ctor_set(x_2067, 1, x_2065);
return x_2067;
}
}
else
{
lean_object* x_2068; lean_object* x_2069; 
x_2068 = lean_ctor_get(x_8, 0);
lean_inc(x_2068);
lean_dec(x_8);
lean_inc(x_1456);
x_2069 = l_Lean_Elab_Term_isDefEq(x_2068, x_3, x_1456, x_2059);
if (lean_obj_tag(x_2069) == 0)
{
lean_object* x_2070; lean_object* x_2071; 
x_2070 = lean_ctor_get(x_2069, 1);
lean_inc(x_2070);
lean_dec(x_2069);
x_2071 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1534, x_1456, x_2070);
lean_dec(x_12);
if (lean_obj_tag(x_2071) == 0)
{
lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; 
x_2072 = lean_ctor_get(x_2071, 1);
lean_inc(x_2072);
if (lean_is_exclusive(x_2071)) {
 lean_ctor_release(x_2071, 0);
 lean_ctor_release(x_2071, 1);
 x_2073 = x_2071;
} else {
 lean_dec_ref(x_2071);
 x_2073 = lean_box(0);
}
if (lean_is_scalar(x_2073)) {
 x_2074 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2074 = x_2073;
}
lean_ctor_set(x_2074, 0, x_2);
lean_ctor_set(x_2074, 1, x_2072);
return x_2074;
}
else
{
lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; 
lean_dec(x_2);
x_2075 = lean_ctor_get(x_2071, 0);
lean_inc(x_2075);
x_2076 = lean_ctor_get(x_2071, 1);
lean_inc(x_2076);
if (lean_is_exclusive(x_2071)) {
 lean_ctor_release(x_2071, 0);
 lean_ctor_release(x_2071, 1);
 x_2077 = x_2071;
} else {
 lean_dec_ref(x_2071);
 x_2077 = lean_box(0);
}
if (lean_is_scalar(x_2077)) {
 x_2078 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2078 = x_2077;
}
lean_ctor_set(x_2078, 0, x_2075);
lean_ctor_set(x_2078, 1, x_2076);
return x_2078;
}
}
else
{
lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; 
lean_dec(x_1456);
lean_dec(x_12);
lean_dec(x_2);
x_2079 = lean_ctor_get(x_2069, 0);
lean_inc(x_2079);
x_2080 = lean_ctor_get(x_2069, 1);
lean_inc(x_2080);
if (lean_is_exclusive(x_2069)) {
 lean_ctor_release(x_2069, 0);
 lean_ctor_release(x_2069, 1);
 x_2081 = x_2069;
} else {
 lean_dec_ref(x_2069);
 x_2081 = lean_box(0);
}
if (lean_is_scalar(x_2081)) {
 x_2082 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2082 = x_2081;
}
lean_ctor_set(x_2082, 0, x_2079);
lean_ctor_set(x_2082, 1, x_2080);
return x_2082;
}
}
}
}
}
}
else
{
lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; 
lean_dec(x_2039);
lean_dec(x_2035);
lean_dec(x_1532);
lean_dec(x_1531);
lean_dec(x_1530);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_2176 = lean_ctor_get(x_2038, 0);
lean_inc(x_2176);
x_2177 = lean_ctor_get(x_2038, 1);
lean_inc(x_2177);
if (lean_is_exclusive(x_2038)) {
 lean_ctor_release(x_2038, 0);
 lean_ctor_release(x_2038, 1);
 x_2178 = x_2038;
} else {
 lean_dec_ref(x_2038);
 x_2178 = lean_box(0);
}
if (lean_is_scalar(x_2178)) {
 x_2179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2179 = x_2178;
}
lean_ctor_set(x_2179, 0, x_2176);
lean_ctor_set(x_2179, 1, x_2177);
return x_2179;
}
}
}
}
else
{
lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; 
lean_dec(x_1530);
lean_dec(x_3);
x_2180 = lean_ctor_get(x_1535, 0);
lean_inc(x_2180);
lean_dec(x_1535);
x_2181 = l_Lean_Elab_Term_NamedArg_inhabited;
x_2182 = lean_array_get(x_2181, x_11, x_2180);
x_2183 = l_Array_eraseIdx___rarg(x_11, x_2180);
lean_dec(x_2180);
x_2184 = lean_ctor_get(x_2182, 1);
lean_inc(x_2184);
lean_dec(x_2182);
lean_inc(x_1456);
lean_inc(x_2);
x_2185 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2184, x_1531, x_1456, x_1459);
if (lean_obj_tag(x_2185) == 0)
{
lean_object* x_2186; lean_object* x_2187; uint8_t x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; 
x_2186 = lean_ctor_get(x_2185, 0);
lean_inc(x_2186);
x_2187 = lean_ctor_get(x_2185, 1);
lean_inc(x_2187);
lean_dec(x_2185);
x_2188 = 1;
x_2189 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_2189, 0, x_6);
lean_ctor_set(x_2189, 1, x_7);
lean_ctor_set(x_2189, 2, x_8);
lean_ctor_set(x_2189, 3, x_10);
lean_ctor_set(x_2189, 4, x_2183);
lean_ctor_set(x_2189, 5, x_12);
lean_ctor_set(x_2189, 6, x_13);
lean_ctor_set_uint8(x_2189, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_2189, sizeof(void*)*7 + 1, x_2188);
lean_inc(x_2186);
x_2190 = l_Lean_mkApp(x_2, x_2186);
x_2191 = lean_expr_instantiate1(x_1532, x_2186);
lean_dec(x_2186);
lean_dec(x_1532);
lean_inc(x_1456);
x_2192 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1458, x_1456, x_2187);
if (lean_obj_tag(x_2192) == 0)
{
lean_object* x_2193; 
x_2193 = lean_ctor_get(x_2192, 1);
lean_inc(x_2193);
lean_dec(x_2192);
x_1 = x_2189;
x_2 = x_2190;
x_3 = x_2191;
x_4 = x_1456;
x_5 = x_2193;
goto _start;
}
else
{
lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; 
lean_dec(x_2191);
lean_dec(x_2190);
lean_dec(x_2189);
lean_dec(x_1456);
x_2195 = lean_ctor_get(x_2192, 0);
lean_inc(x_2195);
x_2196 = lean_ctor_get(x_2192, 1);
lean_inc(x_2196);
if (lean_is_exclusive(x_2192)) {
 lean_ctor_release(x_2192, 0);
 lean_ctor_release(x_2192, 1);
 x_2197 = x_2192;
} else {
 lean_dec_ref(x_2192);
 x_2197 = lean_box(0);
}
if (lean_is_scalar(x_2197)) {
 x_2198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2198 = x_2197;
}
lean_ctor_set(x_2198, 0, x_2195);
lean_ctor_set(x_2198, 1, x_2196);
return x_2198;
}
}
else
{
lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; 
lean_dec(x_2183);
lean_dec(x_1532);
lean_dec(x_1458);
lean_dec(x_1456);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_2199 = lean_ctor_get(x_2185, 0);
lean_inc(x_2199);
x_2200 = lean_ctor_get(x_2185, 1);
lean_inc(x_2200);
if (lean_is_exclusive(x_2185)) {
 lean_ctor_release(x_2185, 0);
 lean_ctor_release(x_2185, 1);
 x_2201 = x_2185;
} else {
 lean_dec_ref(x_2185);
 x_2201 = lean_box(0);
}
if (lean_is_scalar(x_2201)) {
 x_2202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2202 = x_2201;
}
lean_ctor_set(x_2202, 0, x_2199);
lean_ctor_set(x_2202, 1, x_2200);
return x_2202;
}
}
}
else
{
lean_object* x_2203; 
lean_dec(x_13);
lean_dec(x_6);
x_2203 = lean_box(0);
x_1460 = x_2203;
goto block_1529;
}
block_1529:
{
uint8_t x_1461; 
lean_dec(x_1460);
x_1461 = l_Array_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_1461 == 0)
{
lean_object* x_1462; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_inc(x_1456);
x_1462 = l___private_Lean_Elab_App_4__tryCoeFun(x_1458, x_2, x_1456, x_1459);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; 
x_1463 = lean_ctor_get(x_1462, 0);
lean_inc(x_1463);
x_1464 = lean_ctor_get(x_1462, 1);
lean_inc(x_1464);
lean_dec(x_1462);
lean_inc(x_1456);
lean_inc(x_1463);
x_1465 = l_Lean_Elab_Term_inferType(x_1463, x_1456, x_1464);
if (lean_obj_tag(x_1465) == 0)
{
lean_object* x_1466; lean_object* x_1467; 
x_1466 = lean_ctor_get(x_1465, 0);
lean_inc(x_1466);
x_1467 = lean_ctor_get(x_1465, 1);
lean_inc(x_1467);
lean_dec(x_1465);
x_2 = x_1463;
x_3 = x_1466;
x_4 = x_1456;
x_5 = x_1467;
goto _start;
}
else
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; 
lean_dec(x_1463);
lean_dec(x_1456);
lean_dec(x_1);
x_1469 = lean_ctor_get(x_1465, 0);
lean_inc(x_1469);
x_1470 = lean_ctor_get(x_1465, 1);
lean_inc(x_1470);
if (lean_is_exclusive(x_1465)) {
 lean_ctor_release(x_1465, 0);
 lean_ctor_release(x_1465, 1);
 x_1471 = x_1465;
} else {
 lean_dec_ref(x_1465);
 x_1471 = lean_box(0);
}
if (lean_is_scalar(x_1471)) {
 x_1472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1472 = x_1471;
}
lean_ctor_set(x_1472, 0, x_1469);
lean_ctor_set(x_1472, 1, x_1470);
return x_1472;
}
}
else
{
lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; 
lean_dec(x_1456);
lean_dec(x_1);
x_1473 = lean_ctor_get(x_1462, 0);
lean_inc(x_1473);
x_1474 = lean_ctor_get(x_1462, 1);
lean_inc(x_1474);
if (lean_is_exclusive(x_1462)) {
 lean_ctor_release(x_1462, 0);
 lean_ctor_release(x_1462, 1);
 x_1475 = x_1462;
} else {
 lean_dec_ref(x_1462);
 x_1475 = lean_box(0);
}
if (lean_is_scalar(x_1475)) {
 x_1476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1476 = x_1475;
}
lean_ctor_set(x_1476, 0, x_1473);
lean_ctor_set(x_1476, 1, x_1474);
return x_1476;
}
}
else
{
lean_object* x_1477; uint8_t x_1478; 
x_1477 = lean_array_get_size(x_7);
lean_dec(x_7);
x_1478 = lean_nat_dec_eq(x_10, x_1477);
lean_dec(x_1477);
lean_dec(x_10);
if (x_1478 == 0)
{
lean_object* x_1479; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_inc(x_1456);
x_1479 = l___private_Lean_Elab_App_4__tryCoeFun(x_1458, x_2, x_1456, x_1459);
if (lean_obj_tag(x_1479) == 0)
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
x_1480 = lean_ctor_get(x_1479, 0);
lean_inc(x_1480);
x_1481 = lean_ctor_get(x_1479, 1);
lean_inc(x_1481);
lean_dec(x_1479);
lean_inc(x_1456);
lean_inc(x_1480);
x_1482 = l_Lean_Elab_Term_inferType(x_1480, x_1456, x_1481);
if (lean_obj_tag(x_1482) == 0)
{
lean_object* x_1483; lean_object* x_1484; 
x_1483 = lean_ctor_get(x_1482, 0);
lean_inc(x_1483);
x_1484 = lean_ctor_get(x_1482, 1);
lean_inc(x_1484);
lean_dec(x_1482);
x_2 = x_1480;
x_3 = x_1483;
x_4 = x_1456;
x_5 = x_1484;
goto _start;
}
else
{
lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; 
lean_dec(x_1480);
lean_dec(x_1456);
lean_dec(x_1);
x_1486 = lean_ctor_get(x_1482, 0);
lean_inc(x_1486);
x_1487 = lean_ctor_get(x_1482, 1);
lean_inc(x_1487);
if (lean_is_exclusive(x_1482)) {
 lean_ctor_release(x_1482, 0);
 lean_ctor_release(x_1482, 1);
 x_1488 = x_1482;
} else {
 lean_dec_ref(x_1482);
 x_1488 = lean_box(0);
}
if (lean_is_scalar(x_1488)) {
 x_1489 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1489 = x_1488;
}
lean_ctor_set(x_1489, 0, x_1486);
lean_ctor_set(x_1489, 1, x_1487);
return x_1489;
}
}
else
{
lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; 
lean_dec(x_1456);
lean_dec(x_1);
x_1490 = lean_ctor_get(x_1479, 0);
lean_inc(x_1490);
x_1491 = lean_ctor_get(x_1479, 1);
lean_inc(x_1491);
if (lean_is_exclusive(x_1479)) {
 lean_ctor_release(x_1479, 0);
 lean_ctor_release(x_1479, 1);
 x_1492 = x_1479;
} else {
 lean_dec_ref(x_1479);
 x_1492 = lean_box(0);
}
if (lean_is_scalar(x_1492)) {
 x_1493 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1493 = x_1492;
}
lean_ctor_set(x_1493, 0, x_1490);
lean_ctor_set(x_1493, 1, x_1491);
return x_1493;
}
}
else
{
lean_object* x_1494; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; uint8_t x_1525; 
lean_dec(x_1458);
lean_dec(x_1);
x_1521 = l_Lean_Elab_Term_getOptions(x_1456, x_1459);
x_1522 = lean_ctor_get(x_1521, 0);
lean_inc(x_1522);
x_1523 = lean_ctor_get(x_1521, 1);
lean_inc(x_1523);
lean_dec(x_1521);
x_1524 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1525 = l_Lean_checkTraceOption(x_1522, x_1524);
lean_dec(x_1522);
if (x_1525 == 0)
{
x_1494 = x_1523;
goto block_1520;
}
else
{
lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
lean_inc(x_2);
x_1526 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1526, 0, x_2);
x_1527 = l_Lean_Elab_Term_logTrace(x_1524, x_1526, x_1456, x_1523);
x_1528 = lean_ctor_get(x_1527, 1);
lean_inc(x_1528);
lean_dec(x_1527);
x_1494 = x_1528;
goto block_1520;
}
block_1520:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1495; lean_object* x_1496; 
lean_dec(x_3);
x_1495 = lean_unsigned_to_nat(0u);
x_1496 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1495, x_1456, x_1494);
lean_dec(x_12);
if (lean_obj_tag(x_1496) == 0)
{
lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
x_1497 = lean_ctor_get(x_1496, 1);
lean_inc(x_1497);
if (lean_is_exclusive(x_1496)) {
 lean_ctor_release(x_1496, 0);
 lean_ctor_release(x_1496, 1);
 x_1498 = x_1496;
} else {
 lean_dec_ref(x_1496);
 x_1498 = lean_box(0);
}
if (lean_is_scalar(x_1498)) {
 x_1499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1499 = x_1498;
}
lean_ctor_set(x_1499, 0, x_2);
lean_ctor_set(x_1499, 1, x_1497);
return x_1499;
}
else
{
lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; 
lean_dec(x_2);
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
lean_object* x_1504; lean_object* x_1505; 
x_1504 = lean_ctor_get(x_8, 0);
lean_inc(x_1504);
lean_dec(x_8);
lean_inc(x_1456);
x_1505 = l_Lean_Elab_Term_isDefEq(x_1504, x_3, x_1456, x_1494);
if (lean_obj_tag(x_1505) == 0)
{
lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; 
x_1506 = lean_ctor_get(x_1505, 1);
lean_inc(x_1506);
lean_dec(x_1505);
x_1507 = lean_unsigned_to_nat(0u);
x_1508 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_12, x_1507, x_1456, x_1506);
lean_dec(x_12);
if (lean_obj_tag(x_1508) == 0)
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; 
x_1509 = lean_ctor_get(x_1508, 1);
lean_inc(x_1509);
if (lean_is_exclusive(x_1508)) {
 lean_ctor_release(x_1508, 0);
 lean_ctor_release(x_1508, 1);
 x_1510 = x_1508;
} else {
 lean_dec_ref(x_1508);
 x_1510 = lean_box(0);
}
if (lean_is_scalar(x_1510)) {
 x_1511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1511 = x_1510;
}
lean_ctor_set(x_1511, 0, x_2);
lean_ctor_set(x_1511, 1, x_1509);
return x_1511;
}
else
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; 
lean_dec(x_2);
x_1512 = lean_ctor_get(x_1508, 0);
lean_inc(x_1512);
x_1513 = lean_ctor_get(x_1508, 1);
lean_inc(x_1513);
if (lean_is_exclusive(x_1508)) {
 lean_ctor_release(x_1508, 0);
 lean_ctor_release(x_1508, 1);
 x_1514 = x_1508;
} else {
 lean_dec_ref(x_1508);
 x_1514 = lean_box(0);
}
if (lean_is_scalar(x_1514)) {
 x_1515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1515 = x_1514;
}
lean_ctor_set(x_1515, 0, x_1512);
lean_ctor_set(x_1515, 1, x_1513);
return x_1515;
}
}
else
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
lean_dec(x_1456);
lean_dec(x_12);
lean_dec(x_2);
x_1516 = lean_ctor_get(x_1505, 0);
lean_inc(x_1516);
x_1517 = lean_ctor_get(x_1505, 1);
lean_inc(x_1517);
if (lean_is_exclusive(x_1505)) {
 lean_ctor_release(x_1505, 0);
 lean_ctor_release(x_1505, 1);
 x_1518 = x_1505;
} else {
 lean_dec_ref(x_1505);
 x_1518 = lean_box(0);
}
if (lean_is_scalar(x_1518)) {
 x_1519 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1519 = x_1518;
}
lean_ctor_set(x_1519, 0, x_1516);
lean_ctor_set(x_1519, 1, x_1517);
return x_1519;
}
}
}
}
}
}
}
else
{
lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; 
lean_dec(x_1456);
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
x_2204 = lean_ctor_get(x_1457, 0);
lean_inc(x_2204);
x_2205 = lean_ctor_get(x_1457, 1);
lean_inc(x_2205);
if (lean_is_exclusive(x_1457)) {
 lean_ctor_release(x_1457, 0);
 lean_ctor_release(x_1457, 1);
 x_2206 = x_1457;
} else {
 lean_dec_ref(x_1457);
 x_2206 = lean_box(0);
}
if (lean_is_scalar(x_2206)) {
 x_2207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2207 = x_2206;
}
lean_ctor_set(x_2207, 0, x_2204);
lean_ctor_set(x_2207, 1, x_2205);
return x_2207;
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
uint8_t x_62; 
x_62 = 0;
x_16 = x_62;
goto block_61;
}
else
{
uint8_t x_63; 
x_63 = l_Array_isEmpty___rarg(x_3);
x_16 = x_63;
goto block_61;
}
block_61:
{
uint8_t x_17; 
if (x_16 == 0)
{
uint8_t x_59; 
x_59 = 0;
x_17 = x_59;
goto block_58;
}
else
{
uint8_t x_60; 
x_60 = 1;
x_17 = x_60;
goto block_58;
}
block_58:
{
lean_object* x_18; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_dec(x_15);
x_40 = l___private_Lean_Elab_App_11__elabAppArgs___closed__2;
x_41 = l_Lean_checkTraceOption(x_38, x_40);
lean_dec(x_38);
if (x_41 == 0)
{
x_18 = x_39;
goto block_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_inc(x_1);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_1);
lean_inc(x_12);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_12);
if (x_5 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = l___private_Lean_Elab_App_11__elabAppArgs___closed__8;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
x_46 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
x_49 = l_Lean_Elab_Term_logTrace(x_40, x_48, x_6, x_39);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_18 = x_50;
goto block_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l___private_Lean_Elab_App_11__elabAppArgs___closed__11;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
x_53 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_43);
x_56 = l_Lean_Elab_Term_logTrace(x_40, x_55, x_6, x_39);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_18 = x_57;
goto block_37;
}
}
block_37:
{
if (x_17 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Elab_Term_tryPostponeIfMVar(x_12, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_6, 9);
lean_inc(x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_empty___closed__1;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_2);
lean_ctor_set(x_25, 5, x_23);
lean_ctor_set(x_25, 6, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*7, x_5);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 1, x_24);
x_26 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_25, x_1, x_12, x_6, x_20);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
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
x_36 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_35, x_1, x_12, x_6, x_18);
return x_36;
}
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_8);
if (x_64 == 0)
{
return x_8;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_8, 0);
x_66 = lean_ctor_get(x_8, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_8);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
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
lean_ctor_set_uint8(x_8, sizeof(void*)*10 + 1, x_446);
x_447 = lean_unsigned_to_nat(0u);
x_448 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_444, x_447, x_7, x_8, x_9);
lean_dec(x_444);
lean_dec(x_1);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; uint8_t x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_449 = lean_ctor_get(x_8, 0);
x_450 = lean_ctor_get(x_8, 1);
x_451 = lean_ctor_get(x_8, 2);
x_452 = lean_ctor_get(x_8, 3);
x_453 = lean_ctor_get(x_8, 4);
x_454 = lean_ctor_get(x_8, 5);
x_455 = lean_ctor_get(x_8, 6);
x_456 = lean_ctor_get(x_8, 7);
x_457 = lean_ctor_get(x_8, 8);
x_458 = lean_ctor_get_uint8(x_8, sizeof(void*)*10);
x_459 = lean_ctor_get_uint8(x_8, sizeof(void*)*10 + 2);
x_460 = lean_ctor_get(x_8, 9);
lean_inc(x_460);
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
x_461 = 0;
x_462 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_462, 0, x_449);
lean_ctor_set(x_462, 1, x_450);
lean_ctor_set(x_462, 2, x_451);
lean_ctor_set(x_462, 3, x_452);
lean_ctor_set(x_462, 4, x_453);
lean_ctor_set(x_462, 5, x_454);
lean_ctor_set(x_462, 6, x_455);
lean_ctor_set(x_462, 7, x_456);
lean_ctor_set(x_462, 8, x_457);
lean_ctor_set(x_462, 9, x_460);
lean_ctor_set_uint8(x_462, sizeof(void*)*10, x_458);
lean_ctor_set_uint8(x_462, sizeof(void*)*10 + 1, x_461);
lean_ctor_set_uint8(x_462, sizeof(void*)*10 + 2, x_459);
x_463 = lean_unsigned_to_nat(0u);
x_464 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_444, x_463, x_7, x_462, x_9);
lean_dec(x_444);
lean_dec(x_1);
return x_464;
}
}
}
else
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_box(0);
x_466 = l___private_Lean_Elab_App_20__elabAppFnId(x_1, x_465, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_466;
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
