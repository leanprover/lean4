// Lean compiler output
// Module: Init.Lean.Elab.TermApp
// Imports: Init.Lean.Elab.Term
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
lean_object* l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_TermApp_16__toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_16__toMessageData(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__1;
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__6;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3;
extern lean_object* l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_18__elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__1;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_7__regTraceClasses___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind___closed__2;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_17__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__8;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1;
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_20__regTraceClasses(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__7;
extern lean_object* l_Lean_stxInh;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_11__addLValArg___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__11;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_3__elabArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__20;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__28;
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__10;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Elab_TermApp_15__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
lean_object* l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__16;
lean_object* l___private_Init_Lean_Elab_TermApp_19__expandApp___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___closed__2;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__14;
extern lean_object* l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_16__toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_17__mergeFailures(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_19__expandApp___main___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__7;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_18__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__7;
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__2;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__19;
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams___boxed(lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_getKind___closed__4;
lean_object* l___private_Init_Lean_Elab_TermApp_3__elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_19__expandApp___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2;
extern lean_object* l_Lean_Parser_Term_id___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_TermApp_19__expandApp___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
extern lean_object* l_Lean_MessageData_Inhabited;
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_TermApp_16__toMessageData___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__2;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__26;
lean_object* l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__4(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__2;
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_20__regTraceClasses___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__1;
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_14__elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__12;
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__13;
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__3;
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__23;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_17__mergeFailures___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_19__expandApp(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__1;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Init_Lean_Elab_TermApp_6__throwLValError(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofArray(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_11__addLValArg___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__12;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__6;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_5__elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__8;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__5;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__5;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2;
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Term_elabSortApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__17;
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__2;
lean_object* l_Lean_Elab_Term_elabSortApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__3;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_9__resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_9__resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__9;
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef(lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___private_Init_Lean_Elab_TermApp_14__elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__4;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__11;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__27;
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__9;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__3;
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__15;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__18;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__8;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__4;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__2;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__1;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__6;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_11__synthesizePendingInstMVar___lambda__1___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__9;
lean_object* l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__5;
uint8_t l_Lean_Position_DecidableEq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_14__elabAppFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__4;
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__10;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__1;
lean_object* l___private_Init_Lean_Elab_TermApp_15__getSuccess(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp(lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__22;
lean_object* l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__1(lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__2;
extern lean_object* l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__2;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3;
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__25;
lean_object* l_Lean_Elab_Term_Arg_inhabited;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Term_addNamedArg___closed__3;
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Term_addNamedArg___closed__6;
x_19 = lean_alloc_ctor(8, 2, 0);
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
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_TermApp_1__consumeDefaultParams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___spec__1(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_3__elabArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = 1;
lean_inc(x_4);
lean_inc(x_7);
x_9 = l_Lean_Elab_Term_elabTerm(x_6, x_7, x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_10);
x_12 = l_Lean_Elab_Term_inferType(x_1, x_10, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_ensureHasType(x_1, x_7, x_13, x_10, x_4, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_24);
x_25 = l_Lean_Elab_Term_inferType(x_1, x_24, x_4, x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_3);
x_29 = l_Lean_Elab_Term_ensureHasType(x_1, x_28, x_26, x_24, x_4, x_27);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_3__elabArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_TermApp_3__elabArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit parameter '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing, unused named arguments ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_8);
x_12 = l_Lean_Elab_Term_whnfForall(x_1, x_8, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 2);
lean_inc(x_43);
x_44 = lean_ctor_get_uint64(x_13, sizeof(void*)*3);
lean_dec(x_13);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__1(x_41, x_6, x_45);
if (lean_obj_tag(x_46) == 0)
{
if (x_4 == 0)
{
uint8_t x_47; lean_object* x_48; 
x_47 = (uint8_t)((x_44 << 24) >> 61);
x_48 = lean_box(x_47);
switch (lean_obj_tag(x_48)) {
case 1:
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
lean_dec(x_8);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_42);
x_50 = 0;
x_51 = lean_box(0);
lean_inc(x_10);
x_52 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_49, x_50, x_51, x_10, x_14);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_expr_instantiate1(x_43, x_53);
lean_dec(x_43);
x_56 = l_Lean_mkApp(x_9, x_53);
x_8 = x_55;
x_9 = x_56;
x_11 = x_54;
goto _start;
}
case 3:
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_41);
lean_dec(x_8);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_42);
x_59 = 1;
x_60 = lean_box(0);
lean_inc(x_10);
x_61 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_58, x_59, x_60, x_10, x_14);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Expr_mvarId_x21(x_62);
x_65 = lean_array_push(x_7, x_64);
x_66 = lean_expr_instantiate1(x_43, x_62);
lean_dec(x_43);
x_67 = l_Lean_mkApp(x_9, x_62);
x_7 = x_65;
x_8 = x_66;
x_9 = x_67;
x_11 = x_63;
goto _start;
}
default: 
{
lean_object* x_69; uint8_t x_70; 
lean_dec(x_48);
x_69 = lean_array_get_size(x_2);
x_70 = lean_nat_dec_lt(x_5, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_5);
x_71 = l_Array_isEmpty___rarg(x_6);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_72 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_72, 0, x_41);
x_73 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__6;
x_74 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__9;
x_76 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__2(x_45, x_6);
x_78 = l_Array_toList___rarg(x_77);
lean_dec(x_77);
x_79 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_78);
x_80 = l_Array_HasRepr___rarg___closed__1;
x_81 = lean_string_append(x_80, x_79);
lean_dec(x_79);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_Term_throwError___rarg(x_1, x_84, x_10, x_14);
lean_dec(x_10);
lean_dec(x_1);
return x_85;
}
else
{
lean_object* x_86; 
lean_dec(x_41);
lean_dec(x_6);
lean_inc(x_10);
x_86 = l_Lean_Elab_Term_ensureHasType(x_1, x_3, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___spec__1(x_1, x_7, x_45, x_10, x_88);
lean_dec(x_7);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_87);
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
return x_89;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_89, 0);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_89);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_86);
if (x_98 == 0)
{
return x_86;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_86, 0);
x_100 = lean_ctor_get(x_86, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_86);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_41);
lean_dec(x_8);
x_102 = lean_array_fget(x_2, x_5);
lean_inc(x_10);
x_103 = l___private_Init_Lean_Elab_TermApp_3__elabArg(x_1, x_102, x_42, x_10, x_14);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_5, x_106);
lean_dec(x_5);
x_108 = lean_expr_instantiate1(x_43, x_104);
lean_dec(x_43);
x_109 = l_Lean_mkApp(x_9, x_104);
x_5 = x_107;
x_8 = x_108;
x_9 = x_109;
x_11 = x_105;
goto _start;
}
else
{
uint8_t x_111; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_103);
if (x_111 == 0)
{
return x_103;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_103, 0);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_103);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
}
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_array_get_size(x_2);
x_116 = lean_nat_dec_lt(x_5, x_115);
lean_dec(x_115);
if (x_116 == 0)
{
uint8_t x_117; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_5);
x_117 = l_Array_isEmpty___rarg(x_6);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_118 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_118, 0, x_41);
x_119 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__6;
x_120 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__9;
x_122 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__2(x_45, x_6);
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
x_130 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_130, 0, x_122);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Elab_Term_throwError___rarg(x_1, x_130, x_10, x_14);
lean_dec(x_10);
lean_dec(x_1);
return x_131;
}
else
{
lean_object* x_132; 
lean_dec(x_41);
lean_dec(x_6);
lean_inc(x_10);
x_132 = l_Lean_Elab_Term_ensureHasType(x_1, x_3, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___spec__1(x_1, x_7, x_45, x_10, x_134);
lean_dec(x_7);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_133);
return x_135;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_133);
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
uint8_t x_144; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_132);
if (x_144 == 0)
{
return x_132;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_132, 0);
x_146 = lean_ctor_get(x_132, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_132);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_41);
lean_dec(x_8);
x_148 = lean_array_fget(x_2, x_5);
lean_inc(x_10);
x_149 = l___private_Init_Lean_Elab_TermApp_3__elabArg(x_1, x_148, x_42, x_10, x_14);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_add(x_5, x_152);
lean_dec(x_5);
x_154 = lean_expr_instantiate1(x_43, x_150);
lean_dec(x_43);
x_155 = l_Lean_mkApp(x_9, x_150);
x_5 = x_153;
x_8 = x_154;
x_9 = x_155;
x_11 = x_151;
goto _start;
}
else
{
uint8_t x_157; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_149);
if (x_157 == 0)
{
return x_149;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_149, 0);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_149);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_41);
lean_dec(x_8);
x_161 = lean_ctor_get(x_46, 0);
lean_inc(x_161);
lean_dec(x_46);
x_162 = l_Lean_Elab_Term_NamedArg_inhabited;
x_163 = lean_array_get(x_162, x_6, x_161);
x_164 = l_Array_eraseIdx___rarg(x_6, x_161);
lean_dec(x_161);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_10);
x_166 = l___private_Init_Lean_Elab_TermApp_3__elabArg(x_1, x_165, x_42, x_10, x_14);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_expr_instantiate1(x_43, x_167);
lean_dec(x_43);
x_170 = l_Lean_mkApp(x_9, x_167);
x_6 = x_164;
x_8 = x_169;
x_9 = x_170;
x_11 = x_168;
goto _start;
}
else
{
uint8_t x_172; 
lean_dec(x_164);
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_166);
if (x_172 == 0)
{
return x_166;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_166, 0);
x_174 = lean_ctor_get(x_166, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_166);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
else
{
lean_object* x_176; 
lean_dec(x_13);
x_176 = lean_box(0);
x_15 = x_176;
goto block_40;
}
block_40:
{
uint8_t x_16; 
lean_dec(x_15);
x_16 = l_Array_isEmpty___rarg(x_6);
lean_dec(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_17 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__3;
x_18 = l_Lean_Elab_Term_throwError___rarg(x_1, x_17, x_10, x_14);
lean_dec(x_10);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_get_size(x_2);
x_20 = lean_nat_dec_eq(x_5, x_19);
lean_dec(x_19);
lean_dec(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_21 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__3;
x_22 = l_Lean_Elab_Term_throwError___rarg(x_1, x_21, x_10, x_14);
lean_dec(x_10);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_10);
x_23 = l_Lean_Elab_Term_ensureHasType(x_1, x_3, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_2__synthesizeAppInstMVars___spec__1(x_1, x_7, x_26, x_10, x_25);
lean_dec(x_7);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_12);
if (x_177 == 0)
{
return x_12;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_12, 0);
x_179 = lean_ctor_get(x_12, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_12);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_inferType(x_1, x_2, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_15 = l_Lean_Elab_Term_tryPostponeIfMVar(x_13, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_empty___closed__1;
x_19 = l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main(x_1, x_4, x_5, x_6, x_17, x_3, x_18, x_13, x_2, x_7, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_5__elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lean_indentExpr(x_7);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_MessageData_ofList___closed__3;
x_11 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
x_13 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = l_Lean_indentExpr(x_14);
x_16 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Term_throwError___rarg(x_1, x_16, x_5, x_6);
return x_17;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_6__throwLValError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure has only ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" field(s)");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure expected");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, index must be greater than 0");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid \"field\" because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__23;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getOp");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__27;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_44 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__15;
x_45 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_44, x_5, x_20);
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
x_31 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__9;
x_32 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__12;
x_34 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_34, x_5, x_22);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_26);
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
x_50 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__18;
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
x_78 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_79 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_81 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_82, 0, x_65);
x_83 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Elab_Term_mkConst___closed__4;
x_85 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_85, x_5, x_73);
return x_86;
}
else
{
lean_object* x_87; 
lean_dec(x_75);
lean_dec(x_57);
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
x_95 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_96 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_98 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_99, 0, x_65);
x_100 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Elab_Term_mkConst___closed__4;
x_102 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_102, x_5, x_73);
return x_103;
}
else
{
lean_object* x_104; 
lean_dec(x_92);
lean_dec(x_57);
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
x_113 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_114 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_116 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_117, 0, x_65);
x_118 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Elab_Term_mkConst___closed__4;
x_120 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_120, x_5, x_108);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_110);
lean_dec(x_57);
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
x_131 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_132 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_134 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_135, 0, x_65);
x_136 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Elab_Term_mkConst___closed__4;
x_138 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_138, x_5, x_108);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_128);
lean_dec(x_57);
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
x_161 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_162 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_164 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_165, 0, x_148);
x_166 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Elab_Term_mkConst___closed__4;
x_168 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_168, x_5, x_156);
return x_169;
}
else
{
lean_object* x_170; 
lean_dec(x_158);
lean_dec(x_57);
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
x_178 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_179 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_181 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_182, 0, x_148);
x_183 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_Elab_Term_mkConst___closed__4;
x_185 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_185, x_5, x_156);
return x_186;
}
else
{
lean_object* x_187; 
lean_dec(x_175);
lean_dec(x_57);
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
x_196 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_197 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_199 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_200, 0, x_148);
x_201 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_Elab_Term_mkConst___closed__4;
x_203 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_203, x_5, x_191);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_193);
lean_dec(x_57);
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
x_214 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_215 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
x_216 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_217 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_218, 0, x_148);
x_219 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_Elab_Term_mkConst___closed__4;
x_221 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_221, x_5, x_191);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_211);
lean_dec(x_57);
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
x_248 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_249 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_251 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_252, 0, x_235);
x_253 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = l_Lean_Elab_Term_mkConst___closed__4;
x_255 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
x_256 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_255, x_5, x_242);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_245);
lean_dec(x_57);
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
x_266 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_267 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_269 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_270, 0, x_235);
x_271 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_Elab_Term_mkConst___closed__4;
x_273 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_273, x_5, x_242);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_263);
lean_dec(x_57);
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
x_296 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_297 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_295);
x_298 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_299 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_300, 0, x_283);
x_301 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_Elab_Term_mkConst___closed__4;
x_303 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_303, x_5, x_290);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_293);
lean_dec(x_57);
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
x_314 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21;
x_315 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
x_316 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24;
x_317 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_318, 0, x_283);
x_319 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_Elab_Term_mkConst___closed__4;
x_321 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
x_322 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_321, x_5, x_290);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; 
lean_dec(x_311);
lean_dec(x_57);
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
x_337 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__25;
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
x_341 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__28;
x_342 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
x_343 = l_Lean_Elab_Term_mkConst___closed__4;
x_344 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
x_345 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_344, x_5, x_336);
return x_345;
}
else
{
lean_object* x_346; 
lean_dec(x_339);
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
x_349 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__25;
x_350 = lean_name_mk_string(x_331, x_349);
lean_inc(x_350);
x_351 = lean_environment_find(x_347, x_350);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_332);
x_352 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_352, 0, x_350);
x_353 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__28;
x_354 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = l_Lean_Elab_Term_mkConst___closed__4;
x_356 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
x_357 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_356, x_5, x_348);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_351);
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
x_8 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__6;
x_9 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_8, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__3;
x_11 = l___private_Init_Lean_Elab_TermApp_6__throwLValError___rarg(x_1, x_2, x_3, x_10, x_5, x_6);
return x_11;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 2);
x_12 = l_PersistentArray_push___rarg(x_11, x_9);
lean_ctor_set(x_4, 2, x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
lean_dec(x_2);
x_2 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get(x_4, 3);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_ctor_get(x_4, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_22 = l_PersistentArray_push___rarg(x_18, x_9);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_4 = x_23;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_2);
x_13 = l___private_Init_Lean_Elab_TermApp_7__resolveLValAux(x_1, x_2, x_9, x_3, x_6, x_12);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_inc(x_6);
x_17 = l_Lean_Elab_Term_unfoldDefinition_x3f(x_1, x_9, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main___spec__1(x_5, x_20, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_array_push(x_5, x_16);
x_4 = x_27;
x_5 = x_28;
x_7 = x_26;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
}
else
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
return x_8;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_8, 0);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_9__resolveLVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l___private_Init_Lean_Elab_TermApp_8__resolveLValLoop___main(x_1, x_2, x_3, x_7, x_9, x_4, x_8);
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
lean_object* l___private_Init_Lean_Elab_TermApp_9__resolveLVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_TermApp_9__resolveLVal(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("self");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_14 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_mkOptionalNode___closed__1;
x_17 = lean_array_push(x_16, x_15);
x_18 = lean_box(0);
x_19 = l_Array_empty___closed__1;
x_20 = 0;
lean_inc(x_4);
lean_inc(x_1);
x_21 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_11, x_17, x_19, x_18, x_20, x_4, x_12);
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
lean_object* _init_l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field in parent structure");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__3;
x_12 = l_Lean_Elab_Term_throwError___rarg(x_1, x_11, x_5, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1(x_1, x_4, x_13, x_5, x_9);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_11__addLValArg___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, function '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have explicit argument with type (");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ...)");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, insufficient number of arguments for '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_31 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_11__addLValArg___main___spec__1(x_23, x_7, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Expr_isAppOf(x_24, x_2);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_array_get_size(x_5);
x_34 = lean_nat_dec_lt(x_6, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_3);
x_36 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__12;
x_37 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Elab_Term_mkConst___closed__4;
x_39 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Term_throwError___rarg(x_1, x_39, x_9, x_10);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_6, x_41);
lean_dec(x_6);
x_6 = x_42;
x_8 = x_25;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_4);
x_45 = l_Array_insertAt___rarg(x_5, x_6, x_44);
lean_dec(x_6);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_10);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_31, 0);
lean_inc(x_47);
lean_dec(x_31);
x_48 = l_Array_eraseIdx___rarg(x_7, x_47);
lean_dec(x_47);
x_7 = x_48;
x_8 = x_25;
goto _start;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = lean_box(0);
x_11 = x_50;
goto block_22;
}
block_22:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_3);
x_13 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__3;
x_14 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__6;
x_16 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__9;
x_20 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Term_throwError___rarg(x_1, x_20, x_9, x_10);
return x_21;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_11__addLValArg___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_TermApp_11__addLValArg___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_11__addLValArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_TermApp_11__addLValArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idx");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_6, x_2, x_3, x_4, x_5, x_8, x_9);
lean_dec(x_3);
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
x_13 = l___private_Init_Lean_Elab_TermApp_9__resolveLVal(x_1, x_6, x_11, x_8, x_9);
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
x_19 = l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections(x_1, x_16, x_17, x_6, x_8, x_15);
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
x_29 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_mkOptionalNode___closed__1;
x_32 = lean_array_push(x_31, x_30);
x_33 = lean_box(0);
x_34 = l_Array_empty___closed__1;
x_35 = 0;
lean_inc(x_8);
lean_inc(x_1);
x_36 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_25, x_32, x_34, x_33, x_35, x_8, x_26);
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
x_45 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_Term_addNamedArg(x_1, x_2, x_46, x_8, x_26);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_25, x_48, x_3, x_4, x_5, x_8, x_49);
lean_dec(x_3);
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
x_77 = l_Lean_mkOptionalNode___closed__1;
x_78 = lean_array_push(x_77, x_76);
x_79 = lean_box(0);
x_80 = l_Array_empty___closed__1;
x_81 = 0;
lean_inc(x_8);
lean_inc(x_1);
x_82 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_73, x_80, x_78, x_79, x_81, x_8, x_74);
lean_dec(x_78);
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
lean_inc(x_2);
x_94 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main(x_1, x_69, x_70, x_6, x_3, x_93, x_2, x_91, x_8, x_92);
lean_dec(x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_73, x_2, x_95, x_4, x_5, x_8, x_96);
lean_dec(x_95);
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
x_116 = l_Lean_mkOptionalNode___closed__1;
x_117 = lean_array_push(x_116, x_115);
x_118 = lean_box(0);
x_119 = l_Array_empty___closed__1;
x_120 = 0;
lean_inc(x_8);
lean_inc(x_1);
x_121 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_113, x_119, x_117, x_118, x_120, x_8, x_110);
lean_dec(x_117);
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
lean_inc(x_2);
x_133 = l___private_Init_Lean_Elab_TermApp_11__addLValArg___main(x_1, x_111, x_112, x_6, x_3, x_132, x_2, x_130, x_8, x_131);
lean_dec(x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_113, x_2, x_134, x_4, x_5, x_8, x_135);
lean_dec(x_134);
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
x_154 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2;
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_147);
x_157 = l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__2;
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_160 = lean_array_push(x_159, x_155);
x_161 = lean_array_push(x_160, x_158);
x_162 = lean_box(0);
x_163 = l_Array_empty___closed__1;
x_164 = 0;
lean_inc(x_8);
lean_inc(x_1);
x_165 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_150, x_161, x_163, x_162, x_164, x_8, x_151);
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
x_174 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2;
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
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
x_180 = l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__2;
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = l_Lean_Elab_Term_addNamedArg(x_1, x_177, x_181, x_8, x_178);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l___private_Init_Lean_Elab_TermApp_5__elabAppArgs(x_1, x_150, x_183, x_3, x_4, x_5, x_8, x_184);
lean_dec(x_3);
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
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of field notation with `@` modifier");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_List_isEmpty___rarg(x_3);
if (x_10 == 0)
{
if (x_7 == 0)
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main(x_1, x_4, x_5, x_6, x_7, x_2, x_3, x_8, x_9);
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
x_12 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__3;
x_13 = l_Lean_Elab_Term_throwError___rarg(x_1, x_12, x_8, x_9);
lean_dec(x_8);
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
x_18 = l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main(x_1, x_4, x_5, x_6, x_7, x_2, x_3, x_8, x_9);
return x_18;
}
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
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
x_11 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(x_8, x_7, x_9, x_10);
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
lean_object* l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__1(x_5);
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
x_11 = l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_16 = l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__1(x_15);
lean_inc(x_2);
x_17 = l_List_append___rarg(x_16, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_14, x_17, x_3, x_4, x_5, x_6, x_9, x_10);
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
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_18, 0, x_30);
x_31 = lean_array_push(x_7, x_18);
x_7 = x_31;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_7, x_35);
x_7 = x_36;
x_8 = x_13;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_18, 0);
lean_dec(x_39);
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_16 = l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__1(x_15);
lean_inc(x_2);
x_17 = l_List_append___rarg(x_16, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_14, x_17, x_3, x_4, x_5, x_6, x_9, x_10);
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
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_18, 0, x_30);
x_31 = lean_array_push(x_7, x_18);
x_7 = x_31;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_7, x_35);
x_7 = x_36;
x_8 = x_13;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_18, 0);
lean_dec(x_39);
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__4(lean_object* x_1) {
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
x_9 = l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__4(x_5);
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
x_15 = l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__4(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = l___private_Init_Lean_Elab_TermApp_14__elabAppFn___main(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12);
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
lean_object* l___private_Init_Lean_Elab_TermApp_14__elabAppFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_2);
x_11 = l_Lean_Syntax_getKind(x_2);
x_12 = l_Lean_choiceKind;
x_13 = lean_name_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_208; lean_object* x_320; uint8_t x_321; 
x_320 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_2);
x_321 = l_Lean_Syntax_isOfKind(x_2, x_320);
if (x_321 == 0)
{
lean_object* x_322; 
x_322 = lean_box(0);
x_208 = x_322;
goto block_319;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_323 = l_Lean_Syntax_getArgs(x_2);
x_324 = lean_array_get_size(x_323);
lean_dec(x_323);
x_325 = lean_unsigned_to_nat(2u);
x_326 = lean_nat_dec_eq(x_324, x_325);
lean_dec(x_324);
if (x_326 == 0)
{
lean_object* x_327; 
x_327 = lean_box(0);
x_208 = x_327;
goto block_319;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_328 = lean_unsigned_to_nat(1u);
x_329 = l_Lean_Syntax_getArg(x_2, x_328);
x_330 = l_Lean_Parser_Term_id___elambda__1___closed__2;
lean_inc(x_329);
x_331 = l_Lean_Syntax_isOfKind(x_329, x_330);
if (x_331 == 0)
{
lean_object* x_332; uint8_t x_333; lean_object* x_334; 
lean_dec(x_329);
x_332 = lean_box(0);
x_333 = 1;
lean_inc(x_9);
x_334 = l_Lean_Elab_Term_elabTerm(x_2, x_332, x_333, x_9, x_10);
if (lean_obj_tag(x_334) == 0)
{
uint8_t x_335; 
x_335 = !lean_is_exclusive(x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_334, 0);
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
x_338 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_336, x_3, x_4, x_5, x_6, x_7, x_9, x_337);
if (lean_obj_tag(x_338) == 0)
{
uint8_t x_339; 
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
lean_object* x_340; 
x_340 = lean_array_push(x_8, x_338);
lean_ctor_set(x_334, 0, x_340);
return x_334;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_341 = lean_ctor_get(x_338, 0);
x_342 = lean_ctor_get(x_338, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_338);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_array_push(x_8, x_343);
lean_ctor_set(x_334, 0, x_344);
return x_334;
}
}
else
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_338, 0);
lean_inc(x_345);
if (lean_obj_tag(x_345) == 0)
{
uint8_t x_346; 
x_346 = !lean_is_exclusive(x_338);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_338, 0);
lean_dec(x_347);
x_348 = lean_ctor_get(x_345, 0);
lean_inc(x_348);
lean_dec(x_345);
lean_ctor_set(x_338, 0, x_348);
x_349 = lean_array_push(x_8, x_338);
lean_ctor_set(x_334, 0, x_349);
return x_334;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_338, 1);
lean_inc(x_350);
lean_dec(x_338);
x_351 = lean_ctor_get(x_345, 0);
lean_inc(x_351);
lean_dec(x_345);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_350);
x_353 = lean_array_push(x_8, x_352);
lean_ctor_set(x_334, 0, x_353);
return x_334;
}
}
else
{
uint8_t x_354; 
lean_free_object(x_334);
lean_dec(x_337);
lean_dec(x_8);
x_354 = !lean_is_exclusive(x_338);
if (x_354 == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_338, 0);
lean_dec(x_355);
return x_338;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_338, 1);
lean_inc(x_356);
lean_dec(x_338);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_345);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_334, 0);
x_359 = lean_ctor_get(x_334, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_334);
lean_inc(x_359);
x_360 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_358, x_3, x_4, x_5, x_6, x_7, x_9, x_359);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_363 = x_360;
} else {
 lean_dec_ref(x_360);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_362);
x_365 = lean_array_push(x_8, x_364);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_359);
return x_366;
}
else
{
lean_object* x_367; 
x_367 = lean_ctor_get(x_360, 0);
lean_inc(x_367);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_368 = lean_ctor_get(x_360, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_369 = x_360;
} else {
 lean_dec_ref(x_360);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_367, 0);
lean_inc(x_370);
lean_dec(x_367);
if (lean_is_scalar(x_369)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_369;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_368);
x_372 = lean_array_push(x_8, x_371);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_359);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_359);
lean_dec(x_8);
x_374 = lean_ctor_get(x_360, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_375 = x_360;
} else {
 lean_dec_ref(x_360);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_367);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
}
}
else
{
uint8_t x_377; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_377 = !lean_is_exclusive(x_334);
if (x_377 == 0)
{
return x_334;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_334, 0);
x_379 = lean_ctor_get(x_334, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_334);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_2);
x_381 = 1;
x_2 = x_329;
x_7 = x_381;
goto _start;
}
}
}
block_207:
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_14);
x_15 = l_Lean_Parser_Term_id___elambda__1___closed__2;
lean_inc(x_2);
x_16 = l_Lean_Syntax_isOfKind(x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(0);
x_18 = 1;
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
lean_inc(x_22);
x_23 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_array_push(x_8, x_23);
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
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_23, 0, x_33);
x_34 = lean_array_push(x_8, x_23);
lean_ctor_set(x_19, 0, x_34);
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_8, x_37);
lean_ctor_set(x_19, 0, x_38);
return x_19;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_19);
lean_dec(x_22);
lean_dec(x_8);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_23, 0);
lean_dec(x_40);
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
lean_inc(x_44);
x_45 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_9, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_8, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_54 = x_45;
} else {
 lean_dec_ref(x_45);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
x_57 = lean_array_push(x_8, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_44);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_44);
lean_dec(x_8);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_60 = x_45;
} else {
 lean_dec_ref(x_45);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
return x_19;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = l_Lean_Syntax_getArgs(x_2);
x_67 = lean_array_get_size(x_66);
lean_dec(x_66);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_nat_dec_eq(x_67, x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_70 = lean_box(0);
x_71 = 1;
lean_inc(x_9);
x_72 = l_Lean_Elab_Term_elabTerm(x_2, x_70, x_71, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
x_76 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_74, x_3, x_4, x_5, x_6, x_7, x_9, x_75);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_array_push(x_8, x_76);
lean_ctor_set(x_72, 0, x_78);
return x_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_76);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_array_push(x_8, x_81);
lean_ctor_set(x_72, 0, x_82);
return x_72;
}
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_76);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_76, 0);
lean_dec(x_85);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec(x_83);
lean_ctor_set(x_76, 0, x_86);
x_87 = lean_array_push(x_8, x_76);
lean_ctor_set(x_72, 0, x_87);
return x_72;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_dec(x_76);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_array_push(x_8, x_90);
lean_ctor_set(x_72, 0, x_91);
return x_72;
}
}
else
{
uint8_t x_92; 
lean_free_object(x_72);
lean_dec(x_75);
lean_dec(x_8);
x_92 = !lean_is_exclusive(x_76);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_76, 0);
lean_dec(x_93);
return x_76;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_76, 1);
lean_inc(x_94);
lean_dec(x_76);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_83);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_72, 0);
x_97 = lean_ctor_get(x_72, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_72);
lean_inc(x_97);
x_98 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_96, x_3, x_4, x_5, x_6, x_7, x_9, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_array_push(x_8, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_97);
return x_104;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_98, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_107 = x_98;
} else {
 lean_dec_ref(x_98);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
lean_dec(x_105);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
x_110 = lean_array_push(x_8, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_97);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_97);
lean_dec(x_8);
x_112 = lean_ctor_get(x_98, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_113 = x_98;
} else {
 lean_dec_ref(x_98);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_72);
if (x_115 == 0)
{
return x_72;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_72, 0);
x_117 = lean_ctor_get(x_72, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_72);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_Syntax_getArg(x_2, x_119);
x_121 = l_Lean_Syntax_getKind___closed__4;
lean_inc(x_120);
x_122 = l_Lean_Syntax_isOfKind(x_120, x_121);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; lean_object* x_125; 
lean_dec(x_120);
x_123 = lean_box(0);
x_124 = 1;
lean_inc(x_9);
x_125 = l_Lean_Elab_Term_elabTerm(x_2, x_123, x_124, x_9, x_10);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
x_129 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_127, x_3, x_4, x_5, x_6, x_7, x_9, x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_array_push(x_8, x_129);
lean_ctor_set(x_125, 0, x_131);
return x_125;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_129, 0);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_129);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_array_push(x_8, x_134);
lean_ctor_set(x_125, 0, x_135);
return x_125;
}
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_129);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_129, 0);
lean_dec(x_138);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
lean_dec(x_136);
lean_ctor_set(x_129, 0, x_139);
x_140 = lean_array_push(x_8, x_129);
lean_ctor_set(x_125, 0, x_140);
return x_125;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_129, 1);
lean_inc(x_141);
lean_dec(x_129);
x_142 = lean_ctor_get(x_136, 0);
lean_inc(x_142);
lean_dec(x_136);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = lean_array_push(x_8, x_143);
lean_ctor_set(x_125, 0, x_144);
return x_125;
}
}
else
{
uint8_t x_145; 
lean_free_object(x_125);
lean_dec(x_128);
lean_dec(x_8);
x_145 = !lean_is_exclusive(x_129);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_129, 0);
lean_dec(x_146);
return x_129;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_129, 1);
lean_inc(x_147);
lean_dec(x_129);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_136);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_125, 0);
x_150 = lean_ctor_get(x_125, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_125);
lean_inc(x_150);
x_151 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_149, x_3, x_4, x_5, x_6, x_7, x_9, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_array_push(x_8, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_150);
return x_157;
}
else
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_151, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_151, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_160 = x_151;
} else {
 lean_dec_ref(x_151);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
lean_dec(x_158);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
x_163 = lean_array_push(x_8, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_150);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_150);
lean_dec(x_8);
x_165 = lean_ctor_get(x_151, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_166 = x_151;
} else {
 lean_dec_ref(x_151);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_158);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_125);
if (x_168 == 0)
{
return x_125;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_125, 0);
x_170 = lean_ctor_get(x_125, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_125);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
if (lean_obj_tag(x_120) == 3)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_172 = lean_ctor_get(x_120, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_120, 3);
lean_inc(x_173);
lean_dec(x_120);
x_174 = lean_unsigned_to_nat(1u);
x_175 = l_Lean_Syntax_getArg(x_2, x_174);
x_176 = l_Lean_Syntax_getArgs(x_175);
lean_dec(x_175);
x_177 = l_Array_isEmpty___rarg(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = l_Lean_stxInh;
x_179 = lean_array_get(x_178, x_176, x_119);
lean_dec(x_176);
x_180 = l_Lean_Elab_Term_elabExplicitUniv(x_179, x_9, x_10);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
lean_inc(x_9);
x_183 = l_Lean_Elab_Term_resolveName(x_2, x_172, x_173, x_181, x_9, x_182);
lean_dec(x_2);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_184, x_9, x_185);
return x_186;
}
else
{
uint8_t x_187; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_183);
if (x_187 == 0)
{
return x_183;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_183, 0);
x_189 = lean_ctor_get(x_183, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_183);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_180);
if (x_191 == 0)
{
return x_180;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_180, 0);
x_193 = lean_ctor_get(x_180, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_180);
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
lean_dec(x_176);
x_195 = lean_box(0);
lean_inc(x_9);
x_196 = l_Lean_Elab_Term_resolveName(x_2, x_172, x_173, x_195, x_9, x_10);
lean_dec(x_2);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_197, x_9, x_198);
return x_199;
}
else
{
uint8_t x_200; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_200 = !lean_is_exclusive(x_196);
if (x_200 == 0)
{
return x_196;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_196, 0);
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_196);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_120);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = l___private_Init_Lean_Elab_Term_11__synthesizePendingInstMVar___lambda__1___closed__1;
x_205 = l_unreachable_x21___rarg(x_204);
x_206 = lean_apply_2(x_205, x_9, x_10);
return x_206;
}
}
}
}
}
block_319:
{
lean_object* x_209; uint8_t x_210; 
lean_dec(x_208);
x_209 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_inc(x_2);
x_210 = l_Lean_Syntax_isOfKind(x_2, x_209);
if (x_210 == 0)
{
lean_object* x_211; uint8_t x_212; 
x_211 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_inc(x_2);
x_212 = l_Lean_Syntax_isOfKind(x_2, x_211);
if (x_212 == 0)
{
lean_object* x_213; 
x_213 = lean_box(0);
x_14 = x_213;
goto block_207;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_214 = l_Lean_Syntax_getArgs(x_2);
x_215 = lean_array_get_size(x_214);
lean_dec(x_214);
x_216 = lean_unsigned_to_nat(4u);
x_217 = lean_nat_dec_eq(x_215, x_216);
lean_dec(x_215);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_box(0);
x_14 = x_218;
goto block_207;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_219 = lean_unsigned_to_nat(0u);
x_220 = l_Lean_Syntax_getArg(x_2, x_219);
x_221 = lean_unsigned_to_nat(2u);
x_222 = l_Lean_Syntax_getArg(x_2, x_221);
lean_dec(x_2);
x_223 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_3);
x_2 = x_220;
x_3 = x_224;
goto _start;
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_226 = l_Lean_Syntax_getArgs(x_2);
x_227 = lean_array_get_size(x_226);
lean_dec(x_226);
x_228 = lean_unsigned_to_nat(3u);
x_229 = lean_nat_dec_eq(x_227, x_228);
if (x_229 == 0)
{
lean_object* x_230; uint8_t x_231; 
x_230 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_inc(x_2);
x_231 = l_Lean_Syntax_isOfKind(x_2, x_230);
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_227);
x_232 = lean_box(0);
x_14 = x_232;
goto block_207;
}
else
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_unsigned_to_nat(4u);
x_234 = lean_nat_dec_eq(x_227, x_233);
lean_dec(x_227);
if (x_234 == 0)
{
lean_object* x_235; 
x_235 = lean_box(0);
x_14 = x_235;
goto block_207;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_unsigned_to_nat(0u);
x_237 = l_Lean_Syntax_getArg(x_2, x_236);
x_238 = lean_unsigned_to_nat(2u);
x_239 = l_Lean_Syntax_getArg(x_2, x_238);
lean_dec(x_2);
x_240 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_3);
x_2 = x_237;
x_3 = x_241;
goto _start;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
lean_dec(x_227);
x_243 = lean_unsigned_to_nat(2u);
x_244 = l_Lean_Syntax_getArg(x_2, x_243);
x_245 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_244);
x_246 = l_Lean_Syntax_isOfKind(x_244, x_245);
if (x_246 == 0)
{
lean_object* x_247; uint8_t x_248; 
x_247 = l_Lean_Syntax_getKind___closed__4;
lean_inc(x_244);
x_248 = l_Lean_Syntax_isOfKind(x_244, x_247);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; lean_object* x_251; 
lean_dec(x_244);
x_249 = lean_box(0);
x_250 = 1;
lean_inc(x_9);
x_251 = l_Lean_Elab_Term_elabTerm(x_2, x_249, x_250, x_9, x_10);
if (lean_obj_tag(x_251) == 0)
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_251, 0);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
x_255 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_253, x_3, x_4, x_5, x_6, x_7, x_9, x_254);
if (lean_obj_tag(x_255) == 0)
{
uint8_t x_256; 
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = lean_array_push(x_8, x_255);
lean_ctor_set(x_251, 0, x_257);
return x_251;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_255, 0);
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_255);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_array_push(x_8, x_260);
lean_ctor_set(x_251, 0, x_261);
return x_251;
}
}
else
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_255, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_255);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_255, 0);
lean_dec(x_264);
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
lean_dec(x_262);
lean_ctor_set(x_255, 0, x_265);
x_266 = lean_array_push(x_8, x_255);
lean_ctor_set(x_251, 0, x_266);
return x_251;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_255, 1);
lean_inc(x_267);
lean_dec(x_255);
x_268 = lean_ctor_get(x_262, 0);
lean_inc(x_268);
lean_dec(x_262);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = lean_array_push(x_8, x_269);
lean_ctor_set(x_251, 0, x_270);
return x_251;
}
}
else
{
uint8_t x_271; 
lean_free_object(x_251);
lean_dec(x_254);
lean_dec(x_8);
x_271 = !lean_is_exclusive(x_255);
if (x_271 == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_255, 0);
lean_dec(x_272);
return x_255;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_255, 1);
lean_inc(x_273);
lean_dec(x_255);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_262);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_251, 0);
x_276 = lean_ctor_get(x_251, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_251);
lean_inc(x_276);
x_277 = l___private_Init_Lean_Elab_TermApp_13__elabAppLVals(x_1, x_275, x_3, x_4, x_5, x_6, x_7, x_9, x_276);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_280 = x_277;
} else {
 lean_dec_ref(x_277);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
x_282 = lean_array_push(x_8, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_276);
return x_283;
}
else
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_277, 0);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_285 = lean_ctor_get(x_277, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_286 = x_277;
} else {
 lean_dec_ref(x_277);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_284, 0);
lean_inc(x_287);
lean_dec(x_284);
if (lean_is_scalar(x_286)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_286;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_285);
x_289 = lean_array_push(x_8, x_288);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_276);
return x_290;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_276);
lean_dec(x_8);
x_291 = lean_ctor_get(x_277, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_292 = x_277;
} else {
 lean_dec_ref(x_277);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_284);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_251);
if (x_294 == 0)
{
return x_251;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_251, 0);
x_296 = lean_ctor_get(x_251, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_251);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = l_Lean_Syntax_getId(x_244);
lean_dec(x_244);
x_299 = l_Lean_Name_components(x_298);
x_300 = l_List_map___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__4(x_299);
x_301 = lean_unsigned_to_nat(0u);
x_302 = l_Lean_Syntax_getArg(x_2, x_301);
lean_dec(x_2);
x_303 = l_List_append___rarg(x_300, x_3);
x_2 = x_302;
x_3 = x_303;
goto _start;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = l_Lean_fieldIdxKind;
x_306 = l_Lean_Syntax_isNatLitAux(x_305, x_244);
lean_dec(x_244);
x_307 = lean_unsigned_to_nat(0u);
x_308 = l_Lean_Syntax_getArg(x_2, x_307);
lean_dec(x_2);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_309 = l_Nat_Inhabited;
x_310 = l_Option_get_x21___rarg___closed__3;
x_311 = lean_panic_fn(x_309, x_310);
x_312 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_312, 0, x_311);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_3);
x_2 = x_308;
x_3 = x_313;
goto _start;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_306, 0);
lean_inc(x_315);
lean_dec(x_306);
x_316 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_3);
x_2 = x_308;
x_3 = x_317;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = l_Lean_Syntax_getArgs(x_2);
x_384 = lean_unsigned_to_nat(0u);
x_385 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_383, x_384, x_8, x_9, x_10);
lean_dec(x_383);
lean_dec(x_2);
return x_385;
}
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_14__elabAppFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Init_Lean_Elab_TermApp_14__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_14__elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_TermApp_14__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_14__elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Init_Lean_Elab_TermApp_14__elabAppFn(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Elab_TermApp_15__getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Elab_TermApp_15__getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_filterAux___main___at___private_Init_Lean_Elab_TermApp_15__getSuccess___spec__1(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_TermApp_16__toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_16__toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_TermApp_16__toMessageData___spec__1(x_8, x_3, x_7);
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
x_18 = l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__2;
x_19 = lean_alloc_ctor(8, 2, 0);
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
x_24 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_26 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_ctor_get(x_1, 4);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_alloc_ctor(8, 2, 0);
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
x_38 = l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__2;
x_39 = lean_alloc_ctor(8, 2, 0);
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
x_44 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_46 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_ctor_get(x_1, 4);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_alloc_ctor(8, 2, 0);
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
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_TermApp_16__toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_TermApp_16__toMessageData___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_16__toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_TermApp_16__toMessageData(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_17__mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = l___private_Init_Lean_Elab_Term_11__synthesizePendingInstMVar___lambda__1___closed__1;
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
x_30 = l___private_Init_Lean_Elab_TermApp_16__toMessageData(x_29, x_1, x_4, x_5);
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
lean_object* _init_l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_17__mergeFailures___spec__1(x_2, x_5, x_1, x_3, x_4);
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
x_10 = l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__3;
x_11 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Elab_Term_throwError___rarg(x_2, x_11, x_3, x_8);
lean_dec(x_3);
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
lean_object* l___private_Init_Lean_Elab_TermApp_17__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_17__mergeFailures___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_17__mergeFailures___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_18__elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_22 = lean_alloc_ctor(5, 2, 0);
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
lean_object* _init_l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_18__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_TermApp_14__elabAppFn___main(x_1, x_2, x_8, x_3, x_4, x_5, x_9, x_10, x_6, x_7);
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
x_18 = l_Array_filterAux___main___at___private_Init_Lean_Elab_TermApp_15__getSuccess___spec__1(x_12, x_17, x_17);
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
x_22 = l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg(x_12, x_2, x_6, x_13);
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
x_29 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_TermApp_18__elabAppAux___spec__1(x_24, x_27, x_17, x_18);
x_30 = l_Lean_MessageData_ofArray(x_29);
lean_dec(x_29);
x_31 = l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__3;
x_32 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Elab_Term_throwError___rarg(x_2, x_32, x_6, x_28);
lean_dec(x_6);
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
lean_object* _init_l___private_Init_Lean_Elab_TermApp_19__expandApp___main___closed__1() {
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
lean_object* l___private_Init_Lean_Elab_TermApp_19__expandApp___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Term_app___elambda__1___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l___private_Init_Lean_Elab_TermApp_19__expandApp___main___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Lean_Syntax_getArgs(x_1);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l___private_Init_Lean_Elab_TermApp_19__expandApp___main___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
lean_inc(x_19);
x_21 = l_Lean_Syntax_isOfKind(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l___private_Init_Lean_Elab_TermApp_19__expandApp___main(x_17, x_2, x_3);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_23, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_19);
x_32 = lean_array_push(x_30, x_31);
lean_ctor_set(x_24, 1, x_32);
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_19);
x_36 = lean_array_push(x_34, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_23, 1, x_37);
return x_22;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
lean_dec(x_23);
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_41 = x_24;
} else {
 lean_dec_ref(x_24);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_19);
x_43 = lean_array_push(x_40, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_22, 0, x_45);
return x_22;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_dec(x_22);
x_47 = lean_ctor_get(x_23, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_48 = x_23;
} else {
 lean_dec_ref(x_23);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_24, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_51 = x_24;
} else {
 lean_dec_ref(x_24);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_19);
x_53 = lean_array_push(x_50, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_46);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_19);
x_57 = !lean_is_exclusive(x_22);
if (x_57 == 0)
{
return x_22;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_22, 0);
x_59 = lean_ctor_get(x_22, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_22);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = l_Lean_Syntax_getArgs(x_19);
x_62 = lean_array_get_size(x_61);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(5u);
x_64 = lean_nat_dec_eq(x_62, x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l___private_Init_Lean_Elab_TermApp_19__expandApp___main(x_17, x_2, x_3);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_65, 0);
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_66, 1);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_67, 1);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_19);
x_75 = lean_array_push(x_73, x_74);
lean_ctor_set(x_67, 1, x_75);
return x_65;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_67, 0);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_67);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_19);
x_79 = lean_array_push(x_77, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_66, 1, x_80);
return x_65;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_66, 0);
lean_inc(x_81);
lean_dec(x_66);
x_82 = lean_ctor_get(x_67, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_67, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_84 = x_67;
} else {
 lean_dec_ref(x_67);
 x_84 = lean_box(0);
}
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_19);
x_86 = lean_array_push(x_83, x_85);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_65, 0, x_88);
return x_65;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_89 = lean_ctor_get(x_65, 1);
lean_inc(x_89);
lean_dec(x_65);
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_91 = x_66;
} else {
 lean_dec_ref(x_66);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_67, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_67, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_94 = x_67;
} else {
 lean_dec_ref(x_67);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_19);
x_96 = lean_array_push(x_93, x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
if (lean_is_scalar(x_91)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_91;
}
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_89);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_19);
x_100 = !lean_is_exclusive(x_65);
if (x_100 == 0)
{
return x_65;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_65, 0);
x_102 = lean_ctor_get(x_65, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_65);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = l_Lean_Syntax_getArg(x_19, x_18);
x_105 = lean_unsigned_to_nat(3u);
x_106 = l_Lean_Syntax_getArg(x_19, x_105);
lean_dec(x_19);
x_107 = l___private_Init_Lean_Elab_TermApp_19__expandApp___main(x_17, x_2, x_3);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = lean_ctor_get(x_108, 1);
lean_dec(x_113);
x_114 = !lean_is_exclusive(x_109);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_109, 0);
x_116 = lean_ctor_get(x_109, 1);
x_117 = l_Lean_Syntax_getId(x_104);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_106);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_Elab_Term_addNamedArg(x_104, x_115, x_119, x_2, x_110);
lean_dec(x_104);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_120, 0);
lean_ctor_set(x_109, 0, x_122);
lean_ctor_set(x_120, 0, x_108);
return x_120;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_120, 0);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_120);
lean_ctor_set(x_109, 0, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_108);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
lean_free_object(x_109);
lean_dec(x_116);
lean_free_object(x_108);
lean_dec(x_112);
x_126 = !lean_is_exclusive(x_120);
if (x_126 == 0)
{
return x_120;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_120, 0);
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_120);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_109, 0);
x_131 = lean_ctor_get(x_109, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_109);
x_132 = l_Lean_Syntax_getId(x_104);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_106);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Elab_Term_addNamedArg(x_104, x_130, x_134, x_2, x_110);
lean_dec(x_104);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_108, 1, x_139);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_108);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_131);
lean_free_object(x_108);
lean_dec(x_112);
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_143 = x_135;
} else {
 lean_dec_ref(x_135);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_108, 0);
lean_inc(x_145);
lean_dec(x_108);
x_146 = lean_ctor_get(x_109, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_109, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_148 = x_109;
} else {
 lean_dec_ref(x_109);
 x_148 = lean_box(0);
}
x_149 = l_Lean_Syntax_getId(x_104);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_106);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_Elab_Term_addNamedArg(x_104, x_146, x_151, x_2, x_110);
lean_dec(x_104);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_148;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_147);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_145);
lean_ctor_set(x_157, 1, x_156);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_154);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
x_159 = lean_ctor_get(x_152, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_152, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_161 = x_152;
} else {
 lean_dec_ref(x_152);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_106);
lean_dec(x_104);
x_163 = !lean_is_exclusive(x_107);
if (x_163 == 0)
{
return x_107;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_107, 0);
x_165 = lean_ctor_get(x_107, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_107);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_19__expandApp___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_TermApp_19__expandApp___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_19__expandApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_TermApp_19__expandApp___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_19__expandApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_TermApp_19__expandApp(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Init_Lean_Elab_TermApp_19__expandApp___main(x_1, x_3, x_4);
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
x_12 = l___private_Init_Lean_Elab_TermApp_18__elabAppAux(x_1, x_9, x_10, x_11, x_2, x_3, x_8);
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
x_2 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
x_2 = l_Lean_Parser_Term_id___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
return x_5;
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
lean_object* l_Lean_Elab_Term_elabSortApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_stxInh;
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Elab_Term_elabLevel(x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_6, x_5, x_12);
x_14 = l_Lean_Syntax_getKind(x_13);
x_15 = l_Lean_Parser_Term_sort___elambda__1___closed__2;
x_16 = lean_name_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_mkLevelSucc(x_11);
x_18 = l_Lean_mkSort(x_17);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_mkSort(x_11);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_6, x_5, x_22);
x_24 = l_Lean_Syntax_getKind(x_23);
x_25 = l_Lean_Parser_Term_sort___elambda__1___closed__2;
x_26 = lean_name_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lean_mkLevelSucc(x_20);
x_28 = l_Lean_mkSort(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_mkSort(x_20);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
lean_object* _init_l___private_Init_Lean_Elab_TermApp_20__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_7__regTraceClasses___closed__2;
x_2 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_TermApp_20__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_TermApp_20__regTraceClasses___closed__1;
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
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_TermApp(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
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
l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__1);
l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__2 = _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__2);
l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__3 = _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__3);
l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__4 = _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__4);
l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__5 = _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__5);
l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__6 = _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__6);
l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__7 = _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__7);
l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__8 = _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__8);
l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__9 = _init_l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_4__elabAppArgsAux___main___closed__9);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__1);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__2 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__2);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__3 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__3);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__4 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__4);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__5 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__5);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__6 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__6);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__7 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__7);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__8 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__8);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__9 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__9);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__10 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__10);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__11 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__11();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__11);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__12 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__12();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__12);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__13 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__13();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__13);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__14 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__14();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__14);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__15 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__15();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__15);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__16 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__16();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__16);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__17 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__17();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__17);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__18 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__18();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__18);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__19 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__19();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__19);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__20 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__20();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__20);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__21);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__22 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__22();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__22);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__23 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__23();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__23);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__24);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__25 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__25();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__25);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__26 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__26();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__26);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__27 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__27();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__27);
l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__28 = _init_l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__28();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_7__resolveLValAux___closed__28);
l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__1);
l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___spec__1___closed__2);
l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__1);
l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__2 = _init_l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__2);
l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__3 = _init_l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_10__mkBaseProjections___closed__3);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__1);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__2 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__2);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__3 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__3);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__4 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__4);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__5 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__5);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__6 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__6);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__7 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__7);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__8 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__8);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__9 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__9);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__10 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__10);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__11 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__11();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__11);
l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__12 = _init_l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__12();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_11__addLValArg___main___closed__12);
l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__1);
l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__2 = _init_l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_12__elabAppLValsAux___main___closed__2);
l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__1);
l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__2 = _init_l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__2);
l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__3 = _init_l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_13__elabAppLVals___closed__3);
l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__1);
l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__2 = _init_l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_16__toMessageData___closed__2);
l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__1);
l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__2 = _init_l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__2);
l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__3 = _init_l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_17__mergeFailures___rarg___closed__3);
l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__1);
l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__2 = _init_l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__2);
l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__3 = _init_l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_18__elabAppAux___closed__3);
l___private_Init_Lean_Elab_TermApp_19__expandApp___main___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_19__expandApp___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_19__expandApp___main___closed__1);
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
l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_TermApp_20__regTraceClasses___closed__1 = _init_l___private_Init_Lean_Elab_TermApp_20__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_TermApp_20__regTraceClasses___closed__1);
res = l___private_Init_Lean_Elab_TermApp_20__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
