// Lean compiler output
// Module: Lean.Elab.Deriving.Basic
// Imports: Lean.Elab.Command
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_processDefDeriving(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__1;
static lean_object* l_Lean_Elab_getOptDerivingClasses___closed__2;
static lean_object* l_Lean_Elab_elabDeriving___closed__8;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__6;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_processDefDeriving___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__5;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__16;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_derivingHandlersRef;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__3;
static lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__1;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__4;
static lean_object* l_Lean_Elab_elabDeriving___lambda__2___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__1;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__2;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_name_append_before(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_631_(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__3(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___lambda__2___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514_(lean_object*);
lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__4;
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__1;
static lean_object* l_Lean_Elab_Term_processDefDeriving___closed__1;
static lean_object* l_Lean_Elab_elabDeriving___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_defaultHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__4;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DerivingClassView_applyHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1___closed__4;
static lean_object* l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__2;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandlerWithArgs(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__3;
static lean_object* l_Lean_Elab_getOptDerivingClasses___closed__1;
static lean_object* l_Lean_Elab_registerDerivingHandlerWithArgs___closed__2;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__11;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__6;
static lean_object* l_Lean_Elab_defaultHandler___closed__5;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__5;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__13;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getOptDerivingClasses(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__5;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___boxed__const__1;
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__5;
static lean_object* l_Lean_Elab_registerDerivingHandlerWithArgs___closed__1;
static lean_object* l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2;
static lean_object* l_Lean_Elab_defaultHandler___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__9;
lean_object* l_Lean_Name_getString_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__9;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__7;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__15;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__2;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__3;
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__8;
lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_defaultHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__2(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__14;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_compileDecl___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__10;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_applyDerivingHandlers___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__4;
static lean_object* l_Lean_Elab_elabDeriving___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Expr_app___override(x_1, x_2);
x_11 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_10, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = l_Lean_Meta_synthInstance(x_12, x_14, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_bindingDomain_x21(x_1);
lean_inc(x_11);
x_12 = lean_is_out_param(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_13 = lean_infer_type(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_isExprDefEqGuarded(x_14, x_11, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__1(x_3, x_2, x_4, x_26, x_6, x_7, x_8, x_9, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_11);
x_37 = 0;
x_38 = lean_box(0);
lean_inc(x_6);
x_39 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_37, x_38, x_6, x_7, x_8, x_9, x_10);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_40);
x_42 = l_Lean_Expr_app___override(x_3, x_40);
x_43 = l_Lean_Expr_bindingBody_x21(x_1);
x_44 = lean_expr_instantiate1(x_43, x_40);
lean_dec(x_43);
x_45 = lean_array_push(x_4, x_40);
x_46 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f(x_2, x_42, x_44, x_45, x_6, x_7, x_8, x_9, x_41);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_whnfD(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Expr_isForall(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_10);
x_16 = lean_box(0);
x_17 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__2(x_12, x_1, x_2, x_4, x_16, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_12);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = l_Lean_Expr_isForall(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__2(x_18, x_1, x_2, x_4, x_23, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_18);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_11 = lean_infer_type(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1;
x_15 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f(x_2, x_9, x_12, x_14, x_3, x_4, x_5, x_6, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_26 = lean_ctor_get(x_7, 11);
x_27 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_26);
lean_inc(x_24);
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
lean_dec(x_7);
x_28 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 2, x_16);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_18);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*12, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*12 + 1, x_27);
x_30 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_9);
lean_dec(x_29);
return x_30;
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__6;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_16);
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_20, x_3, x_16);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_22);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_27, x_3, x_22);
lean_dec(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_34, x_3, x_31);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_40, x_3, x_36);
lean_dec(x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 10);
lean_inc(x_18);
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_19, 0, x_12);
lean_inc(x_16);
x_20 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_20, 0, x_16);
lean_inc(x_12);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_21, 0, x_12);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_12);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_22, 0, x_12);
lean_closure_set(x_22, 1, x_16);
lean_closure_set(x_22, 2, x_17);
lean_inc(x_12);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_16);
lean_closure_set(x_23, 2, x_17);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_st_ref_get(x_7, x_11);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_environment_main_module(x_12);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_13);
lean_ctor_set(x_31, 4, x_14);
lean_ctor_set(x_31, 5, x_15);
x_32 = lean_box(0);
lean_ctor_set(x_25, 1, x_32);
lean_ctor_set(x_25, 0, x_29);
x_33 = lean_apply_2(x_1, x_31, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_st_ref_take(x_7, x_28);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_38, 1);
lean_dec(x_41);
lean_ctor_set(x_38, 1, x_36);
x_42 = lean_st_ref_set(x_7, x_38, x_39);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_dec(x_35);
x_45 = l_List_reverse___rarg(x_44);
x_46 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_6);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_34);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 2);
x_53 = lean_ctor_get(x_38, 3);
x_54 = lean_ctor_get(x_38, 4);
x_55 = lean_ctor_get(x_38, 5);
x_56 = lean_ctor_get(x_38, 6);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_57 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_36);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set(x_57, 3, x_53);
lean_ctor_set(x_57, 4, x_54);
lean_ctor_set(x_57, 5, x_55);
lean_ctor_set(x_57, 6, x_56);
x_58 = lean_st_ref_set(x_7, x_57, x_39);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_35, 1);
lean_inc(x_60);
lean_dec(x_35);
x_61 = l_List_reverse___rarg(x_60);
x_62 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_6);
lean_dec(x_2);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_34);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_33, 0);
lean_inc(x_66);
lean_dec(x_33);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_maxRecDepthErrorMessage;
x_70 = lean_string_dec_eq(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_72 = l_Lean_MessageData_ofFormat(x_71);
x_73 = l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__2(x_67, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_67);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_68);
x_74 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_6);
lean_dec(x_2);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_6);
lean_dec(x_2);
x_75 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg(x_28);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_25, 0);
x_77 = lean_ctor_get(x_25, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_25);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_environment_main_module(x_12);
x_80 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_80, 0, x_24);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_18);
lean_ctor_set(x_80, 3, x_13);
lean_ctor_set(x_80, 4, x_14);
lean_ctor_set(x_80, 5, x_15);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_apply_2(x_1, x_80, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_st_ref_take(x_7, x_77);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_88, 6);
lean_inc(x_95);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 lean_ctor_release(x_88, 6);
 x_96 = x_88;
} else {
 lean_dec_ref(x_88);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 7, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_86);
lean_ctor_set(x_97, 2, x_91);
lean_ctor_set(x_97, 3, x_92);
lean_ctor_set(x_97, 4, x_93);
lean_ctor_set(x_97, 5, x_94);
lean_ctor_set(x_97, 6, x_95);
x_98 = lean_st_ref_set(x_7, x_97, x_89);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_ctor_get(x_85, 1);
lean_inc(x_100);
lean_dec(x_85);
x_101 = l_List_reverse___rarg(x_100);
x_102 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_99);
lean_dec(x_6);
lean_dec(x_2);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_84);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_83, 0);
lean_inc(x_106);
lean_dec(x_83);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_maxRecDepthErrorMessage;
x_110 = lean_string_dec_eq(x_108, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_108);
x_112 = l_Lean_MessageData_ofFormat(x_111);
x_113 = l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__2(x_107, x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_77);
lean_dec(x_107);
return x_113;
}
else
{
lean_object* x_114; 
lean_dec(x_108);
x_114 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3(x_107, x_2, x_3, x_4, x_5, x_6, x_7, x_77);
lean_dec(x_6);
lean_dec(x_2);
return x_114;
}
}
else
{
lean_object* x_115; 
lean_dec(x_6);
lean_dec(x_2);
x_115 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg(x_77);
return x_115;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_processDefDeriving___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inst", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_processDefDeriving(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_20; 
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 2);
x_28 = lean_ctor_get(x_22, 3);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_29 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f(x_1, x_26, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = 0;
x_34 = lean_box(x_33);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_dec(x_29);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = l_Lean_Expr_appFn_x21(x_42);
lean_dec(x_42);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_25, 1);
x_46 = lean_ctor_get(x_25, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_25, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_inc(x_45);
x_49 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_45, x_48);
lean_inc(x_2);
x_50 = l_Lean_Expr_const___override(x_2, x_49);
x_51 = l_Lean_Expr_app___override(x_43, x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_51);
x_52 = l_Lean_Meta_check(x_51, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Elab_Term_processDefDeriving___closed__1;
x_55 = lean_name_append_before(x_2, x_54);
x_56 = l_Lean_Name_getString_x21(x_1);
lean_dec(x_1);
x_57 = lean_name_append_after(x_55, x_56);
x_58 = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName), 3, 1);
lean_closure_set(x_58, 0, x_57);
lean_inc(x_7);
lean_inc(x_3);
x_59 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1(x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_41, 0);
lean_inc(x_65);
lean_dec(x_41);
x_66 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_60);
lean_ctor_set(x_25, 2, x_63);
lean_ctor_set(x_25, 0, x_60);
lean_inc(x_60);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 1, x_48);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_22, 3, x_66);
lean_ctor_set(x_22, 1, x_68);
lean_ctor_set(x_30, 0, x_22);
lean_inc(x_8);
lean_inc(x_7);
x_70 = l_Lean_addAndCompile(x_30, x_7, x_8, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = 0;
x_73 = lean_unsigned_to_nat(1000u);
x_74 = l_Lean_Meta_addInstance(x_60, x_72, x_73, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = 1;
x_78 = lean_box(x_77);
lean_ctor_set(x_74, 0, x_78);
return x_74;
}
else
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_dec(x_74);
x_80 = 1;
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_74, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_dec(x_74);
x_10 = x_83;
x_11 = x_84;
goto block_19;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
lean_dec(x_70);
x_10 = x_85;
x_11 = x_86;
goto block_19;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_66, 0);
x_88 = lean_ctor_get(x_66, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_66);
lean_inc(x_60);
lean_ctor_set(x_25, 2, x_63);
lean_ctor_set(x_25, 0, x_60);
lean_inc(x_60);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_60);
lean_ctor_set(x_89, 1, x_48);
lean_ctor_set(x_22, 3, x_89);
lean_ctor_set(x_22, 1, x_87);
lean_ctor_set(x_30, 0, x_22);
lean_inc(x_8);
lean_inc(x_7);
x_90 = l_Lean_addAndCompile(x_30, x_7, x_8, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = 0;
x_93 = lean_unsigned_to_nat(1000u);
x_94 = l_Lean_Meta_addInstance(x_60, x_92, x_93, x_5, x_6, x_7, x_8, x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = 1;
x_98 = lean_box(x_97);
if (lean_is_scalar(x_96)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_96;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_95);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
lean_dec(x_94);
x_10 = x_100;
x_11 = x_101;
goto block_19;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_90, 1);
lean_inc(x_103);
lean_dec(x_90);
x_10 = x_102;
x_11 = x_103;
goto block_19;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_51);
lean_free_object(x_25);
lean_dec(x_45);
lean_free_object(x_30);
lean_dec(x_41);
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_104 = lean_ctor_get(x_59, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_59, 1);
lean_inc(x_105);
lean_dec(x_59);
x_10 = x_104;
x_11 = x_105;
goto block_19;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_51);
lean_free_object(x_25);
lean_dec(x_45);
lean_free_object(x_30);
lean_dec(x_41);
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_52, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_52, 1);
lean_inc(x_107);
lean_dec(x_52);
x_10 = x_106;
x_11 = x_107;
goto block_19;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_25, 1);
lean_inc(x_108);
lean_dec(x_25);
x_109 = lean_box(0);
lean_inc(x_108);
x_110 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_108, x_109);
lean_inc(x_2);
x_111 = l_Lean_Expr_const___override(x_2, x_110);
x_112 = l_Lean_Expr_app___override(x_43, x_111);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_112);
x_113 = l_Lean_Meta_check(x_112, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lean_Elab_Term_processDefDeriving___closed__1;
x_116 = lean_name_append_before(x_2, x_115);
x_117 = l_Lean_Name_getString_x21(x_1);
lean_dec(x_1);
x_118 = lean_name_append_after(x_116, x_117);
x_119 = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName), 3, 1);
lean_closure_set(x_119, 0, x_118);
lean_inc(x_7);
lean_inc(x_3);
x_120 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1(x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_114);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_41, 0);
lean_inc(x_126);
lean_dec(x_41);
x_127 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_126, x_3, x_4, x_5, x_6, x_7, x_8, x_125);
lean_dec(x_3);
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
lean_inc(x_121);
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_108);
lean_ctor_set(x_131, 2, x_124);
lean_inc(x_121);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_130;
 lean_ctor_set_tag(x_132, 1);
}
lean_ctor_set(x_132, 0, x_121);
lean_ctor_set(x_132, 1, x_109);
lean_ctor_set(x_22, 3, x_132);
lean_ctor_set(x_22, 1, x_128);
lean_ctor_set(x_22, 0, x_131);
lean_ctor_set(x_30, 0, x_22);
lean_inc(x_8);
lean_inc(x_7);
x_133 = l_Lean_addAndCompile(x_30, x_7, x_8, x_129);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = 0;
x_136 = lean_unsigned_to_nat(1000u);
x_137 = l_Lean_Meta_addInstance(x_121, x_135, x_136, x_5, x_6, x_7, x_8, x_134);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
x_140 = 1;
x_141 = lean_box(x_140);
if (lean_is_scalar(x_139)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_139;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_138);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_137, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 1);
lean_inc(x_144);
lean_dec(x_137);
x_10 = x_143;
x_11 = x_144;
goto block_19;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_121);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_145 = lean_ctor_get(x_133, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_133, 1);
lean_inc(x_146);
lean_dec(x_133);
x_10 = x_145;
x_11 = x_146;
goto block_19;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_112);
lean_dec(x_108);
lean_free_object(x_30);
lean_dec(x_41);
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_147 = lean_ctor_get(x_120, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_120, 1);
lean_inc(x_148);
lean_dec(x_120);
x_10 = x_147;
x_11 = x_148;
goto block_19;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_112);
lean_dec(x_108);
lean_free_object(x_30);
lean_dec(x_41);
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_113, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_113, 1);
lean_inc(x_150);
lean_dec(x_113);
x_10 = x_149;
x_11 = x_150;
goto block_19;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_151 = lean_ctor_get(x_30, 0);
lean_inc(x_151);
lean_dec(x_30);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
x_153 = l_Lean_Expr_appFn_x21(x_152);
lean_dec(x_152);
x_154 = lean_ctor_get(x_25, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_155 = x_25;
} else {
 lean_dec_ref(x_25);
 x_155 = lean_box(0);
}
x_156 = lean_box(0);
lean_inc(x_154);
x_157 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_154, x_156);
lean_inc(x_2);
x_158 = l_Lean_Expr_const___override(x_2, x_157);
x_159 = l_Lean_Expr_app___override(x_153, x_158);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_159);
x_160 = l_Lean_Meta_check(x_159, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_Elab_Term_processDefDeriving___closed__1;
x_163 = lean_name_append_before(x_2, x_162);
x_164 = l_Lean_Name_getString_x21(x_1);
lean_dec(x_1);
x_165 = lean_name_append_after(x_163, x_164);
x_166 = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName), 3, 1);
lean_closure_set(x_166, 0, x_165);
lean_inc(x_7);
lean_inc(x_3);
x_167 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1(x_166, x_3, x_4, x_5, x_6, x_7, x_8, x_161);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_159, x_3, x_4, x_5, x_6, x_7, x_8, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_151, 0);
lean_inc(x_173);
lean_dec(x_151);
x_174 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_173, x_3, x_4, x_5, x_6, x_7, x_8, x_172);
lean_dec(x_3);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
lean_inc(x_168);
if (lean_is_scalar(x_155)) {
 x_178 = lean_alloc_ctor(0, 3, 0);
} else {
 x_178 = x_155;
}
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_154);
lean_ctor_set(x_178, 2, x_171);
lean_inc(x_168);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_177;
 lean_ctor_set_tag(x_179, 1);
}
lean_ctor_set(x_179, 0, x_168);
lean_ctor_set(x_179, 1, x_156);
lean_ctor_set(x_22, 3, x_179);
lean_ctor_set(x_22, 1, x_175);
lean_ctor_set(x_22, 0, x_178);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_22);
lean_inc(x_8);
lean_inc(x_7);
x_181 = l_Lean_addAndCompile(x_180, x_7, x_8, x_176);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = 0;
x_184 = lean_unsigned_to_nat(1000u);
x_185 = l_Lean_Meta_addInstance(x_168, x_183, x_184, x_5, x_6, x_7, x_8, x_182);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
x_188 = 1;
x_189 = lean_box(x_188);
if (lean_is_scalar(x_187)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_187;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_186);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_185, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_185, 1);
lean_inc(x_192);
lean_dec(x_185);
x_10 = x_191;
x_11 = x_192;
goto block_19;
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_168);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_193 = lean_ctor_get(x_181, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_181, 1);
lean_inc(x_194);
lean_dec(x_181);
x_10 = x_193;
x_11 = x_194;
goto block_19;
}
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_159);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_151);
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_195 = lean_ctor_get(x_167, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_167, 1);
lean_inc(x_196);
lean_dec(x_167);
x_10 = x_195;
x_11 = x_196;
goto block_19;
}
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_159);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_151);
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_ctor_get(x_160, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_160, 1);
lean_inc(x_198);
lean_dec(x_160);
x_10 = x_197;
x_11 = x_198;
goto block_19;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_199 = lean_ctor_get(x_29, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_29, 1);
lean_inc(x_200);
lean_dec(x_29);
x_10 = x_199;
x_11 = x_200;
goto block_19;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_22, 0);
x_202 = lean_ctor_get(x_22, 1);
x_203 = lean_ctor_get(x_22, 2);
x_204 = lean_ctor_get_uint8(x_22, sizeof(void*)*4);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_205 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f(x_1, x_202, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = 0;
x_210 = lean_box(x_209);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_207);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_212 = lean_ctor_get(x_205, 1);
lean_inc(x_212);
lean_dec(x_205);
x_213 = lean_ctor_get(x_206, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_214 = x_206;
} else {
 lean_dec_ref(x_206);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
x_216 = l_Lean_Expr_appFn_x21(x_215);
lean_dec(x_215);
x_217 = lean_ctor_get(x_201, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 x_218 = x_201;
} else {
 lean_dec_ref(x_201);
 x_218 = lean_box(0);
}
x_219 = lean_box(0);
lean_inc(x_217);
x_220 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_217, x_219);
lean_inc(x_2);
x_221 = l_Lean_Expr_const___override(x_2, x_220);
x_222 = l_Lean_Expr_app___override(x_216, x_221);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_222);
x_223 = l_Lean_Meta_check(x_222, x_5, x_6, x_7, x_8, x_212);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_225 = l_Lean_Elab_Term_processDefDeriving___closed__1;
x_226 = lean_name_append_before(x_2, x_225);
x_227 = l_Lean_Name_getString_x21(x_1);
lean_dec(x_1);
x_228 = lean_name_append_after(x_226, x_227);
x_229 = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName), 3, 1);
lean_closure_set(x_229, 0, x_228);
lean_inc(x_7);
lean_inc(x_3);
x_230 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1(x_229, x_3, x_4, x_5, x_6, x_7, x_8, x_224);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_222, x_3, x_4, x_5, x_6, x_7, x_8, x_232);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_213, 0);
lean_inc(x_236);
lean_dec(x_213);
x_237 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_236, x_3, x_4, x_5, x_6, x_7, x_8, x_235);
lean_dec(x_3);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_240 = x_237;
} else {
 lean_dec_ref(x_237);
 x_240 = lean_box(0);
}
lean_inc(x_231);
if (lean_is_scalar(x_218)) {
 x_241 = lean_alloc_ctor(0, 3, 0);
} else {
 x_241 = x_218;
}
lean_ctor_set(x_241, 0, x_231);
lean_ctor_set(x_241, 1, x_217);
lean_ctor_set(x_241, 2, x_234);
lean_inc(x_231);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_240;
 lean_ctor_set_tag(x_242, 1);
}
lean_ctor_set(x_242, 0, x_231);
lean_ctor_set(x_242, 1, x_219);
x_243 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_238);
lean_ctor_set(x_243, 2, x_203);
lean_ctor_set(x_243, 3, x_242);
lean_ctor_set_uint8(x_243, sizeof(void*)*4, x_204);
if (lean_is_scalar(x_214)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_214;
}
lean_ctor_set(x_244, 0, x_243);
lean_inc(x_8);
lean_inc(x_7);
x_245 = l_Lean_addAndCompile(x_244, x_7, x_8, x_239);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_247 = 0;
x_248 = lean_unsigned_to_nat(1000u);
x_249 = l_Lean_Meta_addInstance(x_231, x_247, x_248, x_5, x_6, x_7, x_8, x_246);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_251 = x_249;
} else {
 lean_dec_ref(x_249);
 x_251 = lean_box(0);
}
x_252 = 1;
x_253 = lean_box(x_252);
if (lean_is_scalar(x_251)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_251;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_250);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_249, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_249, 1);
lean_inc(x_256);
lean_dec(x_249);
x_10 = x_255;
x_11 = x_256;
goto block_19;
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_231);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_257 = lean_ctor_get(x_245, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_245, 1);
lean_inc(x_258);
lean_dec(x_245);
x_10 = x_257;
x_11 = x_258;
goto block_19;
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_222);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_203);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_259 = lean_ctor_get(x_230, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_230, 1);
lean_inc(x_260);
lean_dec(x_230);
x_10 = x_259;
x_11 = x_260;
goto block_19;
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_222);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_203);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_ctor_get(x_223, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_223, 1);
lean_inc(x_262);
lean_dec(x_223);
x_10 = x_261;
x_11 = x_262;
goto block_19;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_263 = lean_ctor_get(x_205, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_205, 1);
lean_inc(x_264);
lean_dec(x_205);
x_10 = x_263;
x_11 = x_264;
goto block_19;
}
}
}
else
{
uint8_t x_265; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_265 = !lean_is_exclusive(x_20);
if (x_265 == 0)
{
lean_object* x_266; uint8_t x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_20, 0);
lean_dec(x_266);
x_267 = 0;
x_268 = lean_box(x_267);
lean_ctor_set(x_20, 0, x_268);
return x_20;
}
else
{
lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_20, 1);
lean_inc(x_269);
lean_dec(x_20);
x_270 = 0;
x_271 = lean_box(x_270);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_269);
return x_272;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_273 = lean_ctor_get(x_20, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_20, 1);
lean_inc(x_274);
lean_dec(x_20);
x_10 = x_273;
x_11 = x_274;
goto block_19;
}
block_19:
{
uint8_t x_12; 
x_12 = l_Lean_Exception_isInterrupt(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Exception_isRuntime(x_10);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_processDefDeriving___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_processDefDeriving(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_631_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_derivingHandlersRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1___closed__1;
x_6 = lean_st_ref_take(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_8, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_box(0);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_2);
x_12 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_1, x_6);
x_13 = lean_st_ref_set(x_5, x_12, x_9);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_18);
lean_ctor_set(x_6, 0, x_2);
x_19 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_8, x_1, x_6);
x_20 = lean_st_ref_set(x_5, x_19, x_9);
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
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_25, x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_25, x_1, x_29);
x_31 = lean_st_ref_set(x_5, x_30, x_26);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_25, x_1, x_37);
x_39 = lean_st_ref_set(x_5, x_38, x_26);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Elab_registerDerivingHandlerWithArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to register deriving handler, it can only be registered during initialization", 84, 84);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_registerDerivingHandlerWithArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_registerDerivingHandlerWithArgs___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandlerWithArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_initializing(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Lean_Elab_registerDerivingHandlerWithArgs___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_Elab_registerDerivingHandlerWithArgs___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1(x_1, x_2, x_14, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_registerDerivingHandler___lambda__1___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_Elab_registerDerivingHandlerWithArgs(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_registerDerivingHandler___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_defaultHandler___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("default handlers have not been implemented yet, class: '", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_defaultHandler___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_defaultHandler___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_defaultHandler___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' types: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_defaultHandler___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_defaultHandler___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_defaultHandler___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_defaultHandler___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_defaultHandler___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_defaultHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = l_Lean_MessageData_ofName(x_1);
x_7 = l_Lean_Elab_defaultHandler___closed__2;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Elab_defaultHandler___closed__4;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_to_list(x_2);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_11, x_12);
x_14 = l_Lean_MessageData_ofList(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_defaultHandler___closed__6;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_17, x_3, x_4, x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_defaultHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_defaultHandler(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_12 = lean_apply_5(x_10, x_1, x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_3);
{
lean_object* _tmp_3 = x_11;
lean_object* _tmp_4 = x_3;
lean_object* _tmp_7 = x_15;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2;
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_defaultHandler(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_applyDerivingHandlers___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1___closed__1;
x_8 = lean_st_ref_get(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_9, x_1);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = l_Lean_Elab_defaultHandler(x_1, x_2, x_4, x_5, x_10);
lean_dec(x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_applyDerivingHandlers___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_15 = l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1(x_2, x_3, x_14, x_13, x_14, x_4, x_5, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Elab_defaultHandler(x_1, x_2, x_4, x_5, x_18);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_applyDerivingHandlers___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_processDefDeriving___boxed), 9, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = l_Lean_Elab_Command_liftTermElabM___rarg(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_1, x_4);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_18 = lean_array_push(x_5, x_16);
x_3 = x_12;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = lean_array_fget(x_1, x_4);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_18 = lean_array_push(x_5, x_16);
x_3 = x_12;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__7(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__8(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_9, x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_11, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_applyDerivingHandlers(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_11 = lean_array_uget(x_2, x_4);
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
x_12 = x_25;
x_13 = x_8;
goto block_20;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_27 = lean_ctor_get(x_5, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_30 = lean_array_fget(x_21, x_22);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
lean_ctor_set(x_5, 1, x_32);
x_45 = lean_box(0);
lean_inc(x_11);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo), 5, 2);
lean_closure_set(x_46, 0, x_11);
lean_closure_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Command_liftCoreM___rarg(x_46, x_6, x_7, x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_array_get_size(x_1);
x_51 = lean_nat_dec_eq(x_50, x_31);
x_52 = l_Lean_Elab_Command_getRef(x_6, x_7, x_49);
if (x_51 == 0)
{
uint8_t x_119; 
x_119 = 0;
x_53 = x_119;
goto block_118;
}
else
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_120; 
x_120 = 1;
x_53 = x_120;
goto block_118;
}
else
{
uint8_t x_121; 
x_121 = 0;
x_53 = x_121;
goto block_118;
}
}
block_118:
{
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_50);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = l_Lean_replaceRef(x_11, x_54);
lean_dec(x_54);
lean_dec(x_11);
x_57 = lean_ctor_get(x_6, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_6, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_6, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_6, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_6, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_6, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 7);
lean_inc(x_63);
x_64 = lean_ctor_get(x_6, 8);
lean_inc(x_64);
x_65 = lean_ctor_get(x_6, 9);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_67 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_58);
lean_ctor_set(x_67, 2, x_59);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_61);
lean_ctor_set(x_67, 5, x_62);
lean_ctor_set(x_67, 6, x_56);
lean_ctor_set(x_67, 7, x_63);
lean_ctor_set(x_67, 8, x_64);
lean_ctor_set(x_67, 9, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*10, x_66);
lean_inc(x_7);
lean_inc(x_1);
x_68 = l_Lean_Elab_applyDerivingHandlers(x_48, x_1, x_30, x_67, x_7, x_55);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_5);
x_12 = x_70;
x_13 = x_69;
goto block_20;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_33 = x_71;
x_34 = x_72;
goto block_44;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_73 = lean_ctor_get(x_52, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_52, 1);
lean_inc(x_74);
lean_dec(x_52);
x_75 = l_Lean_replaceRef(x_11, x_73);
lean_dec(x_73);
lean_dec(x_11);
x_76 = lean_ctor_get(x_6, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_6, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_6, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_6, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_6, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_6, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_6, 7);
lean_inc(x_82);
x_83 = lean_ctor_get(x_6, 8);
lean_inc(x_83);
x_84 = lean_ctor_get(x_6, 9);
lean_inc(x_84);
x_85 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_86 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_77);
lean_ctor_set(x_86, 2, x_78);
lean_ctor_set(x_86, 3, x_79);
lean_ctor_set(x_86, 4, x_80);
lean_ctor_set(x_86, 5, x_81);
lean_ctor_set(x_86, 6, x_75);
lean_ctor_set(x_86, 7, x_82);
lean_ctor_set(x_86, 8, x_83);
lean_ctor_set(x_86, 9, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*10, x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_lt(x_87, x_50);
lean_dec(x_50);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = l_Lean_instInhabitedName;
x_90 = l_outOfBounds___rarg(x_89);
lean_inc(x_48);
x_91 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(x_48, x_90, x_86, x_7, x_74);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
lean_inc(x_7);
lean_inc(x_1);
x_95 = l_Lean_Elab_applyDerivingHandlers(x_48, x_1, x_30, x_86, x_7, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_5);
x_12 = x_97;
x_13 = x_96;
goto block_20;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_33 = x_98;
x_34 = x_99;
goto block_44;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_86);
lean_dec(x_48);
lean_dec(x_30);
x_100 = lean_ctor_get(x_91, 1);
lean_inc(x_100);
lean_dec(x_91);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_5);
x_12 = x_101;
x_13 = x_100;
goto block_20;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_86);
lean_dec(x_48);
lean_dec(x_30);
x_102 = lean_ctor_get(x_91, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_91, 1);
lean_inc(x_103);
lean_dec(x_91);
x_33 = x_102;
x_34 = x_103;
goto block_44;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_array_fget(x_1, x_87);
lean_inc(x_48);
x_105 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(x_48, x_104, x_86, x_7, x_74);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
lean_inc(x_7);
lean_inc(x_1);
x_109 = l_Lean_Elab_applyDerivingHandlers(x_48, x_1, x_30, x_86, x_7, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_5);
x_12 = x_111;
x_13 = x_110;
goto block_20;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_dec(x_109);
x_33 = x_112;
x_34 = x_113;
goto block_44;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_86);
lean_dec(x_48);
lean_dec(x_30);
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
lean_dec(x_105);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_5);
x_12 = x_115;
x_13 = x_114;
goto block_20;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_86);
lean_dec(x_48);
lean_dec(x_30);
x_116 = lean_ctor_get(x_105, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_dec(x_105);
x_33 = x_116;
x_34 = x_117;
goto block_44;
}
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_30);
lean_dec(x_11);
x_122 = !lean_is_exclusive(x_47);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_47, 0);
x_124 = lean_ctor_get(x_47, 1);
x_125 = l_Lean_Exception_isInterrupt(x_123);
if (x_125 == 0)
{
lean_object* x_126; 
lean_free_object(x_47);
lean_inc(x_6);
x_126 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_123, x_6, x_7, x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_5);
x_12 = x_128;
x_13 = x_127;
goto block_20;
}
else
{
uint8_t x_129; 
lean_dec(x_5);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
return x_126;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_126);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_47;
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_47, 0);
x_134 = lean_ctor_get(x_47, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_47);
x_135 = l_Lean_Exception_isInterrupt(x_133);
if (x_135 == 0)
{
lean_object* x_136; 
lean_inc(x_6);
x_136 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_133, x_6, x_7, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_5);
x_12 = x_138;
x_13 = x_137;
goto block_20;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_5);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_141 = x_136;
} else {
 lean_dec_ref(x_136);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; 
lean_dec(x_5);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_133);
lean_ctor_set(x_143, 1, x_134);
return x_143;
}
}
}
block_44:
{
uint8_t x_35; 
x_35 = l_Lean_Exception_isInterrupt(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
lean_inc(x_6);
x_36 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_33, x_6, x_7, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_5);
x_12 = x_38;
x_13 = x_37;
goto block_20;
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_5);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_34);
return x_43;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_5);
x_144 = lean_array_fget(x_21, x_22);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_add(x_22, x_145);
lean_dec(x_22);
x_147 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_147, 0, x_21);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_23);
x_160 = lean_box(0);
lean_inc(x_11);
x_161 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo), 5, 2);
lean_closure_set(x_161, 0, x_11);
lean_closure_set(x_161, 1, x_160);
x_162 = l_Lean_Elab_Command_liftCoreM___rarg(x_161, x_6, x_7, x_8);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_array_get_size(x_1);
x_166 = lean_nat_dec_eq(x_165, x_145);
x_167 = l_Lean_Elab_Command_getRef(x_6, x_7, x_164);
if (x_166 == 0)
{
uint8_t x_234; 
x_234 = 0;
x_168 = x_234;
goto block_233;
}
else
{
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_235; 
x_235 = 1;
x_168 = x_235;
goto block_233;
}
else
{
uint8_t x_236; 
x_236 = 0;
x_168 = x_236;
goto block_233;
}
}
block_233:
{
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_165);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = l_Lean_replaceRef(x_11, x_169);
lean_dec(x_169);
lean_dec(x_11);
x_172 = lean_ctor_get(x_6, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_6, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_6, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_6, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_6, 4);
lean_inc(x_176);
x_177 = lean_ctor_get(x_6, 5);
lean_inc(x_177);
x_178 = lean_ctor_get(x_6, 7);
lean_inc(x_178);
x_179 = lean_ctor_get(x_6, 8);
lean_inc(x_179);
x_180 = lean_ctor_get(x_6, 9);
lean_inc(x_180);
x_181 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_182 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_182, 0, x_172);
lean_ctor_set(x_182, 1, x_173);
lean_ctor_set(x_182, 2, x_174);
lean_ctor_set(x_182, 3, x_175);
lean_ctor_set(x_182, 4, x_176);
lean_ctor_set(x_182, 5, x_177);
lean_ctor_set(x_182, 6, x_171);
lean_ctor_set(x_182, 7, x_178);
lean_ctor_set(x_182, 8, x_179);
lean_ctor_set(x_182, 9, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*10, x_181);
lean_inc(x_7);
lean_inc(x_1);
x_183 = l_Lean_Elab_applyDerivingHandlers(x_163, x_1, x_144, x_182, x_7, x_170);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_147);
x_12 = x_185;
x_13 = x_184;
goto block_20;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
lean_dec(x_183);
x_148 = x_186;
x_149 = x_187;
goto block_159;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_188 = lean_ctor_get(x_167, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_167, 1);
lean_inc(x_189);
lean_dec(x_167);
x_190 = l_Lean_replaceRef(x_11, x_188);
lean_dec(x_188);
lean_dec(x_11);
x_191 = lean_ctor_get(x_6, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_6, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_6, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_6, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_6, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_6, 5);
lean_inc(x_196);
x_197 = lean_ctor_get(x_6, 7);
lean_inc(x_197);
x_198 = lean_ctor_get(x_6, 8);
lean_inc(x_198);
x_199 = lean_ctor_get(x_6, 9);
lean_inc(x_199);
x_200 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_201 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set(x_201, 4, x_195);
lean_ctor_set(x_201, 5, x_196);
lean_ctor_set(x_201, 6, x_190);
lean_ctor_set(x_201, 7, x_197);
lean_ctor_set(x_201, 8, x_198);
lean_ctor_set(x_201, 9, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*10, x_200);
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_nat_dec_lt(x_202, x_165);
lean_dec(x_165);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = l_Lean_instInhabitedName;
x_205 = l_outOfBounds___rarg(x_204);
lean_inc(x_163);
x_206 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(x_163, x_205, x_201, x_7, x_189);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
lean_inc(x_7);
lean_inc(x_1);
x_210 = l_Lean_Elab_applyDerivingHandlers(x_163, x_1, x_144, x_201, x_7, x_209);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_147);
x_12 = x_212;
x_13 = x_211;
goto block_20;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_210, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
lean_dec(x_210);
x_148 = x_213;
x_149 = x_214;
goto block_159;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_201);
lean_dec(x_163);
lean_dec(x_144);
x_215 = lean_ctor_get(x_206, 1);
lean_inc(x_215);
lean_dec(x_206);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_147);
x_12 = x_216;
x_13 = x_215;
goto block_20;
}
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_201);
lean_dec(x_163);
lean_dec(x_144);
x_217 = lean_ctor_get(x_206, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_206, 1);
lean_inc(x_218);
lean_dec(x_206);
x_148 = x_217;
x_149 = x_218;
goto block_159;
}
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_array_fget(x_1, x_202);
lean_inc(x_163);
x_220 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(x_163, x_219, x_201, x_7, x_189);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
lean_inc(x_7);
lean_inc(x_1);
x_224 = l_Lean_Elab_applyDerivingHandlers(x_163, x_1, x_144, x_201, x_7, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_147);
x_12 = x_226;
x_13 = x_225;
goto block_20;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
lean_dec(x_224);
x_148 = x_227;
x_149 = x_228;
goto block_159;
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_201);
lean_dec(x_163);
lean_dec(x_144);
x_229 = lean_ctor_get(x_220, 1);
lean_inc(x_229);
lean_dec(x_220);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_147);
x_12 = x_230;
x_13 = x_229;
goto block_20;
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_201);
lean_dec(x_163);
lean_dec(x_144);
x_231 = lean_ctor_get(x_220, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_220, 1);
lean_inc(x_232);
lean_dec(x_220);
x_148 = x_231;
x_149 = x_232;
goto block_159;
}
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_dec(x_144);
lean_dec(x_11);
x_237 = lean_ctor_get(x_162, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_162, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_239 = x_162;
} else {
 lean_dec_ref(x_162);
 x_239 = lean_box(0);
}
x_240 = l_Lean_Exception_isInterrupt(x_237);
if (x_240 == 0)
{
lean_object* x_241; 
lean_dec(x_239);
lean_inc(x_6);
x_241 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_237, x_6, x_7, x_238);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_147);
x_12 = x_243;
x_13 = x_242;
goto block_20;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_241, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_246 = x_241;
} else {
 lean_dec_ref(x_241);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
else
{
lean_object* x_248; 
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
if (lean_is_scalar(x_239)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_239;
}
lean_ctor_set(x_248, 0, x_237);
lean_ctor_set(x_248, 1, x_238);
return x_248;
}
}
block_159:
{
uint8_t x_150; 
x_150 = l_Lean_Exception_isInterrupt(x_148);
if (x_150 == 0)
{
lean_object* x_151; 
lean_inc(x_6);
x_151 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_148, x_6, x_7, x_149);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_147);
x_12 = x_153;
x_13 = x_152;
goto block_20;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_156 = x_151;
} else {
 lean_dec_ref(x_151);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; 
lean_dec(x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_148);
lean_ctor_set(x_158, 1, x_149);
return x_158;
}
}
}
}
block_20:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_16;
x_8 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_elabDeriving___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_elabDeriving___lambda__2___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_dec(x_1);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(2u);
lean_inc(x_8);
x_11 = l_Lean_Syntax_matchesNull(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Syntax_getArg(x_8, x_7);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_elabDeriving___lambda__1(x_6, x_15, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = l_Lean_Elab_elabDeriving___lambda__1(x_6, x_18, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("deriving", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_elabDeriving___closed__1;
x_2 = l_Lean_Elab_elabDeriving___closed__2;
x_3 = l_Lean_Elab_elabDeriving___closed__3;
x_4 = l_Lean_Elab_elabDeriving___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_elabDeriving___closed__6;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeriving___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeriving___lambda__3), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_elabDeriving___closed__5;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_67; 
lean_dec(x_11);
lean_dec(x_10);
x_67 = l_Lean_Elab_elabDeriving___closed__6;
x_14 = x_67;
goto block_66;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_11, x_11);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_11);
lean_dec(x_10);
x_69 = l_Lean_Elab_elabDeriving___closed__6;
x_14 = x_69;
goto block_66;
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = 0;
x_71 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_72 = l_Lean_Elab_elabDeriving___closed__7;
x_73 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_10, x_70, x_71, x_72);
lean_dec(x_10);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_14 = x_74;
goto block_66;
}
}
block_66:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Elab_elabDeriving___closed__8;
x_16 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(x_14, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(x_4);
return x_17;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_size(x_18);
x_20 = 0;
lean_inc(x_18);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(x_19, x_20, x_18);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(x_19, x_20, x_18);
x_23 = lean_unsigned_to_nat(4u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_dec(x_1);
x_25 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_lt(x_12, x_26);
if (x_27 == 0)
{
lean_object* x_59; 
lean_dec(x_26);
lean_dec(x_25);
x_59 = l_Lean_Elab_elabDeriving___closed__6;
x_28 = x_59;
goto block_58;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_le(x_26, x_26);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_26);
lean_dec(x_25);
x_61 = l_Lean_Elab_elabDeriving___closed__6;
x_28 = x_61;
goto block_58;
}
else
{
size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_63 = l_Lean_Elab_elabDeriving___closed__7;
x_64 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_25, x_20, x_62, x_63);
lean_dec(x_25);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_28 = x_65;
goto block_58;
}
}
block_58:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Elab_elabDeriving___closed__9;
x_30 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__6(x_28, x_29);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
x_31 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(x_4);
return x_31;
}
else
{
lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_size(x_32);
x_34 = lean_box_usize(x_33);
x_35 = l_Lean_Elab_elabDeriving___boxed__const__1;
x_36 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__8___boxed), 6, 3);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
lean_closure_set(x_36, 2, x_32);
x_37 = l_Lean_Elab_Command_liftCoreM___rarg(x_36, x_2, x_3, x_4);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_array_get_size(x_21);
x_41 = l_Array_toSubarray___rarg(x_21, x_12, x_40);
x_42 = lean_array_size(x_22);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9(x_38, x_22, x_42, x_20, x_41, x_2, x_3, x_39);
lean_dec(x_22);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_37);
if (x_54 == 0)
{
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_37, 0);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_37);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__6(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__8(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__9(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabDeriving___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabDeriving", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_elabDeriving___closed__1;
x_2 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeriving), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__4;
x_3 = l_Lean_Elab_elabDeriving___closed__5;
x_4 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(101u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(114u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(101u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(101u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(39u);
x_3 = l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(51u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 2);
lean_inc(x_16);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_12, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = lean_array_fget(x_14, x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_15, x_24);
lean_dec(x_15);
lean_ctor_set(x_12, 1, x_25);
x_26 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_27 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_10, x_26, x_5, x_6, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_23);
x_31 = lean_array_push(x_13, x_30);
lean_ctor_set(x_4, 1, x_31);
x_32 = 1;
x_33 = lean_usize_add(x_3, x_32);
x_3 = x_33;
x_7 = x_29;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_23);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
x_39 = lean_array_fget(x_14, x_15);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_15, x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_16);
x_43 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_44 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_10, x_43, x_5, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_39);
x_48 = lean_array_push(x_13, x_47);
lean_ctor_set(x_4, 1, x_48);
lean_ctor_set(x_4, 0, x_42);
x_49 = 1;
x_50 = lean_usize_add(x_3, x_49);
x_3 = x_50;
x_7 = x_46;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_42);
lean_dec(x_39);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_54 = x_44;
} else {
 lean_dec_ref(x_44);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc(x_60);
x_61 = lean_nat_dec_lt(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_57);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_7);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
x_65 = lean_array_fget(x_58, x_59);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_59, x_66);
lean_dec(x_59);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 3, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_60);
x_69 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_70 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_10, x_69, x_5, x_6, x_7);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_10);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_65);
x_74 = lean_array_push(x_57, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_74);
x_76 = 1;
x_77 = lean_usize_add(x_3, x_76);
x_3 = x_77;
x_4 = x_75;
x_7 = x_72;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optDeriving", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_elabDeriving___closed__1;
x_2 = l_Lean_Elab_elabDeriving___closed__2;
x_3 = l_Lean_Elab_elabDeriving___closed__3;
x_4 = l_Lean_Elab_getOptDerivingClasses___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getOptDerivingClasses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_getOptDerivingClasses___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(2u);
lean_inc(x_10);
x_12 = l_Lean_Syntax_matchesNull(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_10, x_15);
lean_dec(x_10);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_lt(x_9, x_18);
if (x_19 == 0)
{
lean_object* x_48; 
lean_dec(x_18);
lean_dec(x_17);
x_48 = l_Lean_Elab_elabDeriving___closed__6;
x_20 = x_48;
goto block_47;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_18, x_18);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_18);
lean_dec(x_17);
x_50 = l_Lean_Elab_elabDeriving___closed__6;
x_20 = x_50;
goto block_47;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_53 = l_Lean_Elab_elabDeriving___closed__7;
x_54 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_17, x_51, x_52, x_53);
lean_dec(x_17);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_20 = x_55;
goto block_47;
}
}
block_47:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_elabDeriving___closed__8;
x_22 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(x_20, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
else
{
lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_array_size(x_25);
x_27 = 0;
lean_inc(x_25);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(x_26, x_27, x_25);
x_29 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(x_26, x_27, x_25);
x_30 = lean_array_get_size(x_28);
x_31 = l_Array_toSubarray___rarg(x_28, x_9, x_30);
x_32 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_size(x_29);
x_35 = l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(x_29, x_34, x_27, x_33, x_2, x_3, x_4);
lean_dec(x_29);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DerivingClassView_applyHandlers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_replaceRef(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 6);
lean_dec(x_14);
lean_ctor_set(x_3, 6, x_12);
x_15 = l_Lean_Elab_applyDerivingHandlers(x_7, x_2, x_8, x_3, x_4, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_ctor_get(x_3, 4);
x_21 = lean_ctor_get(x_3, 5);
x_22 = lean_ctor_get(x_3, 7);
x_23 = lean_ctor_get(x_3, 8);
x_24 = lean_ctor_get(x_3, 9);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_19);
lean_ctor_set(x_26, 4, x_20);
lean_ctor_set(x_26, 5, x_21);
lean_ctor_set(x_26, 6, x_12);
lean_ctor_set(x_26, 7, x_22);
lean_ctor_set(x_26, 8, x_23);
lean_ctor_set(x_26, 9, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*10, x_25);
x_27 = l_Lean_Elab_applyDerivingHandlers(x_7, x_2, x_8, x_26, x_4, x_11);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Deriving", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_elabDeriving___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__3;
x_2 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__4;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__6;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__8;
x_2 = l_Lean_Elab_elabDeriving___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__9;
x_2 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__10;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Basic", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__11;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__13;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__15;
x_2 = lean_unsigned_to_nat(2514u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__2;
x_3 = 0;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__16;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1 = _init_l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__3___closed__6);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__4___rarg___closed__2);
l_Lean_Elab_Term_processDefDeriving___closed__1 = _init_l_Lean_Elab_Term_processDefDeriving___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_processDefDeriving___closed__1);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_631_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_derivingHandlersRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_derivingHandlersRef);
lean_dec_ref(res);
}l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1___closed__1 = _init_l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_registerDerivingHandlerWithArgs___lambda__1___closed__1);
l_Lean_Elab_registerDerivingHandlerWithArgs___closed__1 = _init_l_Lean_Elab_registerDerivingHandlerWithArgs___closed__1();
lean_mark_persistent(l_Lean_Elab_registerDerivingHandlerWithArgs___closed__1);
l_Lean_Elab_registerDerivingHandlerWithArgs___closed__2 = _init_l_Lean_Elab_registerDerivingHandlerWithArgs___closed__2();
lean_mark_persistent(l_Lean_Elab_registerDerivingHandlerWithArgs___closed__2);
l_Lean_Elab_defaultHandler___closed__1 = _init_l_Lean_Elab_defaultHandler___closed__1();
lean_mark_persistent(l_Lean_Elab_defaultHandler___closed__1);
l_Lean_Elab_defaultHandler___closed__2 = _init_l_Lean_Elab_defaultHandler___closed__2();
lean_mark_persistent(l_Lean_Elab_defaultHandler___closed__2);
l_Lean_Elab_defaultHandler___closed__3 = _init_l_Lean_Elab_defaultHandler___closed__3();
lean_mark_persistent(l_Lean_Elab_defaultHandler___closed__3);
l_Lean_Elab_defaultHandler___closed__4 = _init_l_Lean_Elab_defaultHandler___closed__4();
lean_mark_persistent(l_Lean_Elab_defaultHandler___closed__4);
l_Lean_Elab_defaultHandler___closed__5 = _init_l_Lean_Elab_defaultHandler___closed__5();
lean_mark_persistent(l_Lean_Elab_defaultHandler___closed__5);
l_Lean_Elab_defaultHandler___closed__6 = _init_l_Lean_Elab_defaultHandler___closed__6();
lean_mark_persistent(l_Lean_Elab_defaultHandler___closed__6);
l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1);
l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2);
l_Lean_Elab_applyDerivingHandlers___closed__1 = _init_l_Lean_Elab_applyDerivingHandlers___closed__1();
lean_mark_persistent(l_Lean_Elab_applyDerivingHandlers___closed__1);
l_Lean_Elab_elabDeriving___lambda__2___closed__1 = _init_l_Lean_Elab_elabDeriving___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_elabDeriving___lambda__2___closed__1);
l_Lean_Elab_elabDeriving___lambda__2___closed__2 = _init_l_Lean_Elab_elabDeriving___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_elabDeriving___lambda__2___closed__2);
l_Lean_Elab_elabDeriving___closed__1 = _init_l_Lean_Elab_elabDeriving___closed__1();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__1);
l_Lean_Elab_elabDeriving___closed__2 = _init_l_Lean_Elab_elabDeriving___closed__2();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__2);
l_Lean_Elab_elabDeriving___closed__3 = _init_l_Lean_Elab_elabDeriving___closed__3();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__3);
l_Lean_Elab_elabDeriving___closed__4 = _init_l_Lean_Elab_elabDeriving___closed__4();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__4);
l_Lean_Elab_elabDeriving___closed__5 = _init_l_Lean_Elab_elabDeriving___closed__5();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__5);
l_Lean_Elab_elabDeriving___closed__6 = _init_l_Lean_Elab_elabDeriving___closed__6();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__6);
l_Lean_Elab_elabDeriving___closed__7 = _init_l_Lean_Elab_elabDeriving___closed__7();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__7);
l_Lean_Elab_elabDeriving___closed__8 = _init_l_Lean_Elab_elabDeriving___closed__8();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__8);
l_Lean_Elab_elabDeriving___closed__9 = _init_l_Lean_Elab_elabDeriving___closed__9();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__9);
l_Lean_Elab_elabDeriving___boxed__const__1 = _init_l_Lean_Elab_elabDeriving___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_elabDeriving___boxed__const__1);
l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1 = _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1);
l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2 = _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2);
l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3 = _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3);
l___regBuiltin_Lean_Elab_elabDeriving__1___closed__4 = _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving__1___closed__4);
l___regBuiltin_Lean_Elab_elabDeriving__1___closed__5 = _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_elabDeriving__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_elabDeriving_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_getOptDerivingClasses___closed__1 = _init_l_Lean_Elab_getOptDerivingClasses___closed__1();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___closed__1);
l_Lean_Elab_getOptDerivingClasses___closed__2 = _init_l_Lean_Elab_getOptDerivingClasses___closed__2();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__8);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__9 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__9();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__9);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__10 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__10();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__10);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__11 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__11();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__11);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__12 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__12();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__12);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__13 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__13();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__13);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__14 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__14();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__14);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__15 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__15();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__15);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__16 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__16();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514____closed__16);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_2514_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
