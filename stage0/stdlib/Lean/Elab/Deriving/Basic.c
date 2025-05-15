// Lean compiler output
// Module: Lean.Elab.Deriving.Basic
// Imports: Lean.Elab.Command Lean.Elab.DeclarationRange
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_processDefDeriving(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__7;
static lean_object* l_Lean_Elab_getOptDerivingClasses___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__2;
lean_object* lean_name_append_after(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_processDefDeriving___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__5;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at_Lean_Elab_Term_processDefDeriving___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_derivingHandlersRef;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__3;
static lean_object* l_Lean_Elab_applyDerivingHandlers___closed__2;
static lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1;
static lean_object* l_Lean_Elab_defaultHandler___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__4;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__5;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_name_append_before(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at_Lean_Elab_Command_runLinters___spec__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_applyDerivingHandlers___closed__3;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__6;
lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_registerDerivingHandler___closed__1;
static lean_object* l_Lean_Elab_elabDeriving___closed__2;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_processDefDeriving___closed__1;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__1;
static lean_object* l_Lean_Elab_elabDeriving___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_defaultHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__4;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_652_(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__1;
static lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__4;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___closed__1;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_is_out_param(lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DerivingClassView_applyHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_registerDerivingHandler___closed__2;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__8;
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__3;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_elabDeriving__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at_Lean_Elab_Term_processDefDeriving___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__2;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937_(lean_object*);
static lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__2;
static lean_object* l_Lean_Elab_getOptDerivingClasses___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__2;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__6;
static lean_object* l_Lean_Elab_defaultHandler___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getOptDerivingClasses(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__11;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__5;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___boxed__const__1;
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__6;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__14;
lean_object* l_Lean_Meta_addInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__3;
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__9;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__7;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__4;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_mkUnusedBaseName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__3___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_defaultHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__10;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_compileDecls_doCompile___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__4;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__3;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_registerDerivingHandler___lambda__1___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_applyDerivingHandlers___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f_go_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_14, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_12, 1, x_18);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_22, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
lean_inc(x_1);
x_15 = l_Lean_Environment_find_x3f(x_13, x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
x_16 = l_Lean_MessageData_ofConstName(x_1, x_14);
x_17 = l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__2(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 0;
lean_inc(x_1);
x_27 = l_Lean_Environment_find_x3f(x_25, x_1, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_Lean_MessageData_ofConstName(x_1, x_26);
x_29 = l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__2(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_24);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_14, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_12, 1, x_18);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_22, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__5(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_26 = lean_ctor_get(x_7, 11);
x_27 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_28 = lean_ctor_get(x_7, 12);
lean_inc(x_28);
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
x_29 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_30 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_30, 2, x_16);
lean_ctor_set(x_30, 3, x_17);
lean_ctor_set(x_30, 4, x_18);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set(x_30, 6, x_20);
lean_ctor_set(x_30, 7, x_21);
lean_ctor_set(x_30, 8, x_22);
lean_ctor_set(x_30, 9, x_23);
lean_ctor_set(x_30, 10, x_24);
lean_ctor_set(x_30, 11, x_26);
lean_ctor_set(x_30, 12, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*13, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*13 + 1, x_27);
x_31 = l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__5(x_2, x_3, x_4, x_5, x_6, x_30, x_8, x_9);
lean_dec(x_30);
return x_31;
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__6;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 1;
x_6 = l_Lean_Environment_contains(x_1, x_2, x_5);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__1___boxed), 4, 1);
lean_closure_set(x_19, 0, x_12);
lean_inc(x_16);
x_20 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_20, 0, x_16);
lean_inc(x_12);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__2___boxed), 4, 1);
lean_closure_set(x_21, 0, x_12);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_12);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__3___boxed), 6, 3);
lean_closure_set(x_22, 0, x_12);
lean_closure_set(x_22, 1, x_16);
lean_closure_set(x_22, 2, x_17);
lean_inc(x_12);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__4___boxed), 6, 3);
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
x_30 = l_Lean_Environment_mainModule(x_12);
lean_dec(x_12);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 2);
x_53 = lean_ctor_get(x_38, 3);
x_54 = lean_ctor_get(x_38, 4);
x_55 = lean_ctor_get(x_38, 5);
x_56 = lean_ctor_get(x_38, 6);
x_57 = lean_ctor_get(x_38, 7);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_58 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_36);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_53);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_55);
lean_ctor_set(x_58, 6, x_56);
lean_ctor_set(x_58, 7, x_57);
x_59 = lean_st_ref_set(x_7, x_58, x_39);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_35, 1);
lean_inc(x_61);
lean_dec(x_35);
x_62 = l_List_reverse___rarg(x_61);
x_63 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_60);
lean_dec(x_6);
lean_dec(x_2);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_34);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_33, 0);
lean_inc(x_67);
lean_dec(x_33);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_maxRecDepthErrorMessage;
x_71 = lean_string_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_69);
x_73 = l_Lean_MessageData_ofFormat(x_72);
x_74 = l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__4(x_68, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_68);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_69);
x_75 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_6);
lean_dec(x_2);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_6);
lean_dec(x_2);
x_76 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg(x_28);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_25, 0);
x_78 = lean_ctor_get(x_25, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_25);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Environment_mainModule(x_12);
lean_dec(x_12);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_24);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_18);
lean_ctor_set(x_81, 3, x_13);
lean_ctor_set(x_81, 4, x_14);
lean_ctor_set(x_81, 5, x_15);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_apply_2(x_1, x_81, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_st_ref_take(x_7, x_78);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 5);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 6);
lean_inc(x_96);
x_97 = lean_ctor_get(x_89, 7);
lean_inc(x_97);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 lean_ctor_release(x_89, 6);
 lean_ctor_release(x_89, 7);
 x_98 = x_89;
} else {
 lean_dec_ref(x_89);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 8, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_91);
lean_ctor_set(x_99, 1, x_87);
lean_ctor_set(x_99, 2, x_92);
lean_ctor_set(x_99, 3, x_93);
lean_ctor_set(x_99, 4, x_94);
lean_ctor_set(x_99, 5, x_95);
lean_ctor_set(x_99, 6, x_96);
lean_ctor_set(x_99, 7, x_97);
x_100 = lean_st_ref_set(x_7, x_99, x_90);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get(x_86, 1);
lean_inc(x_102);
lean_dec(x_86);
x_103 = l_List_reverse___rarg(x_102);
x_104 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__2(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_101);
lean_dec(x_6);
lean_dec(x_2);
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
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_85);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_84, 0);
lean_inc(x_108);
lean_dec(x_84);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_maxRecDepthErrorMessage;
x_112 = lean_string_dec_eq(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_110);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__4(x_109, x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_78);
lean_dec(x_109);
return x_115;
}
else
{
lean_object* x_116; 
lean_dec(x_110);
x_116 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6(x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_78);
lean_dec(x_6);
lean_dec(x_2);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_6);
lean_dec(x_2);
x_117 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg(x_78);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at_Lean_Elab_Term_processDefDeriving___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l_Lean_Syntax_getRange_x3f(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_DeclarationRange_ofStringPositions(x_15, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
lean_ctor_set(x_10, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_dec(x_6);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_DeclarationRange_ofStringPositions(x_21, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_declRangeExt;
return x_1;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__3;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 4);
lean_dec(x_15);
x_16 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__1;
x_17 = l_Lean_MapDeclarationExtension_insert___rarg(x_16, x_14, x_1, x_2);
x_18 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__4;
lean_ctor_set(x_11, 4, x_18);
lean_ctor_set(x_11, 0, x_17);
x_19 = lean_st_ref_set(x_8, x_11, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_6, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 1);
lean_dec(x_25);
x_26 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__5;
lean_ctor_set(x_22, 1, x_26);
x_27 = lean_st_ref_set(x_6, x_22, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 2);
x_36 = lean_ctor_get(x_22, 3);
x_37 = lean_ctor_get(x_22, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_38 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__5;
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_37);
x_40 = lean_st_ref_set(x_6, x_39, x_23);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
x_47 = lean_ctor_get(x_11, 2);
x_48 = lean_ctor_get(x_11, 3);
x_49 = lean_ctor_get(x_11, 5);
x_50 = lean_ctor_get(x_11, 6);
x_51 = lean_ctor_get(x_11, 7);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_52 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__1;
x_53 = l_Lean_MapDeclarationExtension_insert___rarg(x_52, x_45, x_1, x_2);
x_54 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__4;
x_55 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set(x_55, 2, x_47);
lean_ctor_set(x_55, 3, x_48);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_49);
lean_ctor_set(x_55, 6, x_50);
lean_ctor_set(x_55, 7, x_51);
x_56 = lean_st_ref_set(x_8, x_55, x_12);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_st_ref_take(x_6, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 4);
lean_inc(x_64);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 x_65 = x_59;
} else {
 lean_dec_ref(x_59);
 x_65 = lean_box(0);
}
x_66 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__5;
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 5, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_62);
lean_ctor_set(x_67, 3, x_63);
lean_ctor_set(x_67, 4, x_64);
x_68 = lean_st_ref_set(x_6, x_67, x_60);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_8);
x_11 = l_Lean_Elab_getDeclarationRange_x3f___at_Lean_Elab_Term_processDefDeriving___spec__9(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_inc(x_8);
x_21 = l_Lean_Elab_getDeclarationRange_x3f___at_Lean_Elab_Term_processDefDeriving___spec__9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
lean_inc(x_20);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 0, x_20);
x_26 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10(x_1, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
lean_inc(x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_20);
x_29 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_8);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_21, 1);
x_32 = lean_ctor_get(x_21, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
lean_dec(x_22);
lean_ctor_set(x_21, 1, x_33);
lean_ctor_set(x_21, 0, x_20);
x_34 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10(x_1, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_8);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10(x_1, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_8);
return x_38;
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
x_20 = l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_59 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3(x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_60);
x_74 = l_Lean_Meta_addInstance(x_60, x_72, x_73, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get(x_7, 5);
lean_inc(x_76);
x_77 = lean_box(0);
x_78 = l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8(x_60, x_76, x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_75);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_76);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
x_81 = 1;
x_82 = lean_box(x_81);
lean_ctor_set(x_78, 0, x_82);
return x_78;
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_dec(x_78);
x_84 = 1;
x_85 = lean_box(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_87 = lean_ctor_get(x_74, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
lean_dec(x_74);
x_10 = x_87;
x_11 = x_88;
goto block_19;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_89 = lean_ctor_get(x_70, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_70, 1);
lean_inc(x_90);
lean_dec(x_70);
x_10 = x_89;
x_11 = x_90;
goto block_19;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_66, 0);
x_92 = lean_ctor_get(x_66, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_66);
lean_inc(x_60);
lean_ctor_set(x_25, 2, x_63);
lean_ctor_set(x_25, 0, x_60);
lean_inc(x_60);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_60);
lean_ctor_set(x_93, 1, x_48);
lean_ctor_set(x_22, 3, x_93);
lean_ctor_set(x_22, 1, x_91);
lean_ctor_set(x_30, 0, x_22);
lean_inc(x_8);
lean_inc(x_7);
x_94 = l_Lean_addAndCompile(x_30, x_7, x_8, x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = 0;
x_97 = lean_unsigned_to_nat(1000u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_60);
x_98 = l_Lean_Meta_addInstance(x_60, x_96, x_97, x_5, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_ctor_get(x_7, 5);
lean_inc(x_100);
x_101 = lean_box(0);
x_102 = l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8(x_60, x_100, x_101, x_3, x_4, x_5, x_6, x_7, x_8, x_99);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_100);
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
x_105 = 1;
x_106 = lean_box(x_105);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_108 = lean_ctor_get(x_98, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_98, 1);
lean_inc(x_109);
lean_dec(x_98);
x_10 = x_108;
x_11 = x_109;
goto block_19;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_110 = lean_ctor_get(x_94, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_94, 1);
lean_inc(x_111);
lean_dec(x_94);
x_10 = x_110;
x_11 = x_111;
goto block_19;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
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
x_112 = lean_ctor_get(x_59, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_59, 1);
lean_inc(x_113);
lean_dec(x_59);
x_10 = x_112;
x_11 = x_113;
goto block_19;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
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
x_114 = lean_ctor_get(x_52, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_52, 1);
lean_inc(x_115);
lean_dec(x_52);
x_10 = x_114;
x_11 = x_115;
goto block_19;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_25, 1);
lean_inc(x_116);
lean_dec(x_25);
x_117 = lean_box(0);
lean_inc(x_116);
x_118 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_116, x_117);
lean_inc(x_2);
x_119 = l_Lean_Expr_const___override(x_2, x_118);
x_120 = l_Lean_Expr_app___override(x_43, x_119);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_120);
x_121 = l_Lean_Meta_check(x_120, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = l_Lean_Elab_Term_processDefDeriving___closed__1;
x_124 = lean_name_append_before(x_2, x_123);
x_125 = l_Lean_Name_getString_x21(x_1);
lean_dec(x_1);
x_126 = lean_name_append_after(x_124, x_125);
x_127 = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName), 3, 1);
lean_closure_set(x_127, 0, x_126);
lean_inc(x_7);
lean_inc(x_3);
x_128 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3(x_127, x_3, x_4, x_5, x_6, x_7, x_8, x_122);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_120, x_3, x_4, x_5, x_6, x_7, x_8, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_41, 0);
lean_inc(x_134);
lean_dec(x_41);
x_135 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_134, x_3, x_4, x_5, x_6, x_7, x_8, x_133);
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
lean_inc(x_129);
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_129);
lean_ctor_set(x_139, 1, x_116);
lean_ctor_set(x_139, 2, x_132);
lean_inc(x_129);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_138;
 lean_ctor_set_tag(x_140, 1);
}
lean_ctor_set(x_140, 0, x_129);
lean_ctor_set(x_140, 1, x_117);
lean_ctor_set(x_22, 3, x_140);
lean_ctor_set(x_22, 1, x_136);
lean_ctor_set(x_22, 0, x_139);
lean_ctor_set(x_30, 0, x_22);
lean_inc(x_8);
lean_inc(x_7);
x_141 = l_Lean_addAndCompile(x_30, x_7, x_8, x_137);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_143 = 0;
x_144 = lean_unsigned_to_nat(1000u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_129);
x_145 = l_Lean_Meta_addInstance(x_129, x_143, x_144, x_5, x_6, x_7, x_8, x_142);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_ctor_get(x_7, 5);
lean_inc(x_147);
x_148 = lean_box(0);
x_149 = l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8(x_129, x_147, x_148, x_3, x_4, x_5, x_6, x_7, x_8, x_146);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_147);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = 1;
x_153 = lean_box(x_152);
if (lean_is_scalar(x_151)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_151;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_155 = lean_ctor_get(x_145, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_145, 1);
lean_inc(x_156);
lean_dec(x_145);
x_10 = x_155;
x_11 = x_156;
goto block_19;
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_157 = lean_ctor_get(x_141, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_141, 1);
lean_inc(x_158);
lean_dec(x_141);
x_10 = x_157;
x_11 = x_158;
goto block_19;
}
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_120);
lean_dec(x_116);
lean_free_object(x_30);
lean_dec(x_41);
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_159 = lean_ctor_get(x_128, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_128, 1);
lean_inc(x_160);
lean_dec(x_128);
x_10 = x_159;
x_11 = x_160;
goto block_19;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_120);
lean_dec(x_116);
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
x_161 = lean_ctor_get(x_121, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_121, 1);
lean_inc(x_162);
lean_dec(x_121);
x_10 = x_161;
x_11 = x_162;
goto block_19;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_163 = lean_ctor_get(x_30, 0);
lean_inc(x_163);
lean_dec(x_30);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
x_165 = l_Lean_Expr_appFn_x21(x_164);
lean_dec(x_164);
x_166 = lean_ctor_get(x_25, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_167 = x_25;
} else {
 lean_dec_ref(x_25);
 x_167 = lean_box(0);
}
x_168 = lean_box(0);
lean_inc(x_166);
x_169 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_166, x_168);
lean_inc(x_2);
x_170 = l_Lean_Expr_const___override(x_2, x_169);
x_171 = l_Lean_Expr_app___override(x_165, x_170);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_171);
x_172 = l_Lean_Meta_check(x_171, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_174 = l_Lean_Elab_Term_processDefDeriving___closed__1;
x_175 = lean_name_append_before(x_2, x_174);
x_176 = l_Lean_Name_getString_x21(x_1);
lean_dec(x_1);
x_177 = lean_name_append_after(x_175, x_176);
x_178 = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName), 3, 1);
lean_closure_set(x_178, 0, x_177);
lean_inc(x_7);
lean_inc(x_3);
x_179 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3(x_178, x_3, x_4, x_5, x_6, x_7, x_8, x_173);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_171, x_3, x_4, x_5, x_6, x_7, x_8, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_ctor_get(x_163, 0);
lean_inc(x_185);
lean_dec(x_163);
x_186 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_185, x_3, x_4, x_5, x_6, x_7, x_8, x_184);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_189 = x_186;
} else {
 lean_dec_ref(x_186);
 x_189 = lean_box(0);
}
lean_inc(x_180);
if (lean_is_scalar(x_167)) {
 x_190 = lean_alloc_ctor(0, 3, 0);
} else {
 x_190 = x_167;
}
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_166);
lean_ctor_set(x_190, 2, x_183);
lean_inc(x_180);
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_189;
 lean_ctor_set_tag(x_191, 1);
}
lean_ctor_set(x_191, 0, x_180);
lean_ctor_set(x_191, 1, x_168);
lean_ctor_set(x_22, 3, x_191);
lean_ctor_set(x_22, 1, x_187);
lean_ctor_set(x_22, 0, x_190);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_22);
lean_inc(x_8);
lean_inc(x_7);
x_193 = l_Lean_addAndCompile(x_192, x_7, x_8, x_188);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = 0;
x_196 = lean_unsigned_to_nat(1000u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_180);
x_197 = l_Lean_Meta_addInstance(x_180, x_195, x_196, x_5, x_6, x_7, x_8, x_194);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; 
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_ctor_get(x_7, 5);
lean_inc(x_199);
x_200 = lean_box(0);
x_201 = l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8(x_180, x_199, x_200, x_3, x_4, x_5, x_6, x_7, x_8, x_198);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_199);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = 1;
x_205 = lean_box(x_204);
if (lean_is_scalar(x_203)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_203;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_202);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_180);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_207 = lean_ctor_get(x_197, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_197, 1);
lean_inc(x_208);
lean_dec(x_197);
x_10 = x_207;
x_11 = x_208;
goto block_19;
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_180);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_209 = lean_ctor_get(x_193, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_193, 1);
lean_inc(x_210);
lean_dec(x_193);
x_10 = x_209;
x_11 = x_210;
goto block_19;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_171);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_163);
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_211 = lean_ctor_get(x_179, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_179, 1);
lean_inc(x_212);
lean_dec(x_179);
x_10 = x_211;
x_11 = x_212;
goto block_19;
}
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_171);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_163);
lean_free_object(x_22);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_172, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_172, 1);
lean_inc(x_214);
lean_dec(x_172);
x_10 = x_213;
x_11 = x_214;
goto block_19;
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; 
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
x_215 = lean_ctor_get(x_29, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_29, 1);
lean_inc(x_216);
lean_dec(x_29);
x_10 = x_215;
x_11 = x_216;
goto block_19;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_22, 0);
x_218 = lean_ctor_get(x_22, 1);
x_219 = lean_ctor_get(x_22, 2);
x_220 = lean_ctor_get_uint8(x_22, sizeof(void*)*4);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_221 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f(x_1, x_218, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_224 = x_221;
} else {
 lean_dec_ref(x_221);
 x_224 = lean_box(0);
}
x_225 = 0;
x_226 = lean_box(x_225);
if (lean_is_scalar(x_224)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_224;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_223);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_228 = lean_ctor_get(x_221, 1);
lean_inc(x_228);
lean_dec(x_221);
x_229 = lean_ctor_get(x_222, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_230 = x_222;
} else {
 lean_dec_ref(x_222);
 x_230 = lean_box(0);
}
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
x_232 = l_Lean_Expr_appFn_x21(x_231);
lean_dec(x_231);
x_233 = lean_ctor_get(x_217, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 x_234 = x_217;
} else {
 lean_dec_ref(x_217);
 x_234 = lean_box(0);
}
x_235 = lean_box(0);
lean_inc(x_233);
x_236 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_233, x_235);
lean_inc(x_2);
x_237 = l_Lean_Expr_const___override(x_2, x_236);
x_238 = l_Lean_Expr_app___override(x_232, x_237);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_238);
x_239 = l_Lean_Meta_check(x_238, x_5, x_6, x_7, x_8, x_228);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_241 = l_Lean_Elab_Term_processDefDeriving___closed__1;
x_242 = lean_name_append_before(x_2, x_241);
x_243 = l_Lean_Name_getString_x21(x_1);
lean_dec(x_1);
x_244 = lean_name_append_after(x_242, x_243);
x_245 = lean_alloc_closure((void*)(l_Lean_Elab_mkUnusedBaseName), 3, 1);
lean_closure_set(x_245, 0, x_244);
lean_inc(x_7);
lean_inc(x_3);
x_246 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3(x_245, x_3, x_4, x_5, x_6, x_7, x_8, x_240);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_238, x_3, x_4, x_5, x_6, x_7, x_8, x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_229, 0);
lean_inc(x_252);
lean_dec(x_229);
x_253 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_252, x_3, x_4, x_5, x_6, x_7, x_8, x_251);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
lean_inc(x_247);
if (lean_is_scalar(x_234)) {
 x_257 = lean_alloc_ctor(0, 3, 0);
} else {
 x_257 = x_234;
}
lean_ctor_set(x_257, 0, x_247);
lean_ctor_set(x_257, 1, x_233);
lean_ctor_set(x_257, 2, x_250);
lean_inc(x_247);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_256;
 lean_ctor_set_tag(x_258, 1);
}
lean_ctor_set(x_258, 0, x_247);
lean_ctor_set(x_258, 1, x_235);
x_259 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_254);
lean_ctor_set(x_259, 2, x_219);
lean_ctor_set(x_259, 3, x_258);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_220);
if (lean_is_scalar(x_230)) {
 x_260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_260 = x_230;
}
lean_ctor_set(x_260, 0, x_259);
lean_inc(x_8);
lean_inc(x_7);
x_261 = l_Lean_addAndCompile(x_260, x_7, x_8, x_255);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec(x_261);
x_263 = 0;
x_264 = lean_unsigned_to_nat(1000u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_247);
x_265 = l_Lean_Meta_addInstance(x_247, x_263, x_264, x_5, x_6, x_7, x_8, x_262);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; 
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
x_267 = lean_ctor_get(x_7, 5);
lean_inc(x_267);
x_268 = lean_box(0);
x_269 = l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8(x_247, x_267, x_268, x_3, x_4, x_5, x_6, x_7, x_8, x_266);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_267);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
x_272 = 1;
x_273 = lean_box(x_272);
if (lean_is_scalar(x_271)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_271;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_270);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_247);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_275 = lean_ctor_get(x_265, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_265, 1);
lean_inc(x_276);
lean_dec(x_265);
x_10 = x_275;
x_11 = x_276;
goto block_19;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_247);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_277 = lean_ctor_get(x_261, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_261, 1);
lean_inc(x_278);
lean_dec(x_261);
x_10 = x_277;
x_11 = x_278;
goto block_19;
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_238);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_279 = lean_ctor_get(x_246, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_246, 1);
lean_inc(x_280);
lean_dec(x_246);
x_10 = x_279;
x_11 = x_280;
goto block_19;
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_238);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = lean_ctor_get(x_239, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_239, 1);
lean_inc(x_282);
lean_dec(x_239);
x_10 = x_281;
x_11 = x_282;
goto block_19;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_283 = lean_ctor_get(x_221, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_221, 1);
lean_inc(x_284);
lean_dec(x_221);
x_10 = x_283;
x_11 = x_284;
goto block_19;
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_20);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_20, 0);
lean_dec(x_286);
x_287 = 0;
x_288 = lean_box(x_287);
lean_ctor_set(x_20, 0, x_288);
return x_20;
}
else
{
lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_20, 1);
lean_inc(x_289);
lean_dec(x_20);
x_290 = 0;
x_291 = lean_box(x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_289);
return x_292;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_293 = lean_ctor_get(x_20, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_20, 1);
lean_inc(x_294);
lean_dec(x_20);
x_10 = x_293;
x_11 = x_294;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_processDefDeriving___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Term_processDefDeriving___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_processDefDeriving___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at_Lean_Elab_Term_processDefDeriving___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_getDeclarationRange_x3f___at_Lean_Elab_Term_processDefDeriving___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_addDeclarationRangesFromSyntax___at_Lean_Elab_Term_processDefDeriving___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_652_(lean_object* x_1) {
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
static lean_object* _init_l_Lean_Elab_registerDerivingHandler___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_derivingHandlersRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Elab_registerDerivingHandler___lambda__1___closed__1;
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
static lean_object* _init_l_Lean_Elab_registerDerivingHandler___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to register deriving handler, it can only be registered during initialization", 84, 84);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_registerDerivingHandler___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_registerDerivingHandler___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_Elab_registerDerivingHandler___closed__2;
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
x_11 = l_Lean_Elab_registerDerivingHandler___closed__2;
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
x_15 = l_Lean_Elab_registerDerivingHandler___lambda__1(x_1, x_2, x_14, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerDerivingHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_registerDerivingHandler___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
x_13 = l_List_mapTR_loop___at_Lean_compileDecls_doCompile___spec__1(x_11, x_12);
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
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_15 = lean_apply_4(x_13, x_1, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_4);
{
lean_object* _tmp_5 = x_14;
lean_object* _tmp_6 = x_4;
lean_object* _tmp_7 = lean_box(0);
lean_object* _tmp_10 = x_18;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_11 = _tmp_10;
}
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2;
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2;
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
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("running deriving handlers for '", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_MessageData_ofName(x_1);
x_7 = l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__2;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__4;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_defaultHandler(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_applyDerivingHandlers___lambda__3___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Elab_registerDerivingHandler___lambda__1___closed__1;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_8, x_1);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Elab_defaultHandler(x_1, x_2, x_3, x_4, x_9);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Elab_applyDerivingHandlers___lambda__3___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_12);
lean_inc(x_2);
x_15 = l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1(x_2, x_12, x_13, x_14, x_12, x_12, x_14, lean_box(0), x_3, x_4, x_9);
lean_dec(x_12);
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
x_19 = l_Lean_Elab_defaultHandler(x_1, x_2, x_3, x_4, x_18);
lean_dec(x_4);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_Elab_applyDerivingHandlers___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_applyDerivingHandlers___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Deriving", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_applyDerivingHandlers___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_applyDerivingHandlers___closed__1;
x_2 = l_Lean_Elab_applyDerivingHandlers___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_applyDerivingHandlers___lambda__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_applyDerivingHandlers___lambda__3), 5, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = l_Lean_Elab_applyDerivingHandlers___closed__3;
x_9 = 1;
x_10 = l_Lean_Elab_defaultHandler___closed__5;
x_11 = l_Lean_withTraceNode___at_Lean_Elab_Command_runLinters___spec__10(x_8, x_6, x_7, x_9, x_10, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_applyDerivingHandlers___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_applyDerivingHandlers___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__2;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_applyDerivingHandlers(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_6, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; lean_object* x_22; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_7);
x_13 = lean_array_uget(x_4, x_6);
x_33 = lean_box(0);
lean_inc(x_13);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo), 5, 2);
lean_closure_set(x_34, 0, x_13);
lean_closure_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Command_liftCoreM___rarg(x_34, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_array_get_size(x_2);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_dec_eq(x_38, x_39);
lean_dec(x_38);
x_41 = l_Lean_Elab_Command_getRef(x_8, x_9, x_37);
if (x_40 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_replaceRef(x_13, x_42);
lean_dec(x_42);
lean_dec(x_13);
x_45 = lean_ctor_get(x_8, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_8, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_8, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_8, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_8, 5);
lean_inc(x_50);
x_51 = lean_ctor_get(x_8, 7);
lean_inc(x_51);
x_52 = lean_ctor_get(x_8, 8);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_8, sizeof(void*)*9);
x_54 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_54, 2, x_47);
lean_ctor_set(x_54, 3, x_48);
lean_ctor_set(x_54, 4, x_49);
lean_ctor_set(x_54, 5, x_50);
lean_ctor_set(x_54, 6, x_44);
lean_ctor_set(x_54, 7, x_51);
lean_ctor_set(x_54, 8, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*9, x_53);
lean_inc(x_9);
lean_inc(x_2);
x_55 = l_Lean_Elab_applyDerivingHandlers(x_36, x_2, x_54, x_9, x_43);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___closed__1;
x_14 = x_57;
x_15 = x_56;
goto block_20;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_21 = x_58;
x_22 = x_59;
goto block_32;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_41, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
lean_dec(x_41);
x_62 = l_Lean_replaceRef(x_13, x_60);
lean_dec(x_60);
lean_dec(x_13);
x_63 = lean_ctor_get(x_8, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_8, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_8, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_8, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_8, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_8, 7);
lean_inc(x_69);
x_70 = lean_ctor_get(x_8, 8);
lean_inc(x_70);
x_71 = lean_ctor_get_uint8(x_8, sizeof(void*)*9);
x_72 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_64);
lean_ctor_set(x_72, 2, x_65);
lean_ctor_set(x_72, 3, x_66);
lean_ctor_set(x_72, 4, x_67);
lean_ctor_set(x_72, 5, x_68);
lean_ctor_set(x_72, 6, x_62);
lean_ctor_set(x_72, 7, x_69);
lean_ctor_set(x_72, 8, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*9, x_71);
x_73 = l_Lean_instInhabitedName;
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get(x_73, x_2, x_74);
lean_inc(x_36);
x_76 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(x_36, x_75, x_72, x_9, x_61);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
lean_inc(x_9);
lean_inc(x_2);
x_80 = l_Lean_Elab_applyDerivingHandlers(x_36, x_2, x_72, x_9, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___closed__1;
x_14 = x_82;
x_15 = x_81;
goto block_20;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_21 = x_83;
x_22 = x_84;
goto block_32;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_72);
lean_dec(x_36);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_dec(x_76);
x_86 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___closed__1;
x_14 = x_86;
x_15 = x_85;
goto block_20;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_72);
lean_dec(x_36);
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_dec(x_76);
x_21 = x_87;
x_22 = x_88;
goto block_32;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_13);
x_89 = lean_ctor_get(x_35, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_35, 1);
lean_inc(x_90);
lean_dec(x_35);
x_21 = x_89;
x_22 = x_90;
goto block_32;
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_6, x_17);
x_6 = x_18;
x_7 = x_16;
x_10 = x_15;
goto _start;
}
block_32:
{
uint8_t x_23; 
x_23 = l_Lean_Exception_isInterrupt(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_8);
x_24 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_21, x_8, x_9, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___closed__1;
x_14 = x_26;
x_15 = x_25;
goto block_20;
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
return x_31;
}
}
}
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; size_t x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = 0;
if (x_13 == 0)
{
lean_object* x_60; 
lean_dec(x_11);
lean_dec(x_10);
x_60 = l_Lean_Elab_elabDeriving___closed__6;
x_15 = x_60;
goto block_59;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_11, x_11);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_11);
lean_dec(x_10);
x_62 = l_Lean_Elab_elabDeriving___closed__6;
x_15 = x_62;
goto block_59;
}
else
{
size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_64 = l_Lean_Elab_elabDeriving___closed__7;
x_65 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_10, x_14, x_63, x_64);
lean_dec(x_10);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_15 = x_66;
goto block_59;
}
}
block_59:
{
size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_array_size(x_15);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__2(x_16, x_14, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(4u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = l_Lean_Syntax_getArgs(x_20);
lean_dec(x_20);
x_22 = lean_array_get_size(x_21);
x_23 = lean_nat_dec_lt(x_12, x_22);
if (x_23 == 0)
{
lean_object* x_52; 
lean_dec(x_22);
lean_dec(x_21);
x_52 = l_Lean_Elab_elabDeriving___closed__6;
x_24 = x_52;
goto block_51;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_22, x_22);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_22);
lean_dec(x_21);
x_54 = l_Lean_Elab_elabDeriving___closed__6;
x_24 = x_54;
goto block_51;
}
else
{
size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_56 = l_Lean_Elab_elabDeriving___closed__7;
x_57 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_21, x_14, x_55, x_56);
lean_dec(x_21);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_24 = x_58;
goto block_51;
}
}
block_51:
{
size_t x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_array_size(x_24);
x_26 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__2(x_25, x_14, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_size(x_27);
x_29 = lean_box_usize(x_28);
x_30 = l_Lean_Elab_elabDeriving___boxed__const__1;
x_31 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__3___boxed), 6, 3);
lean_closure_set(x_31, 0, x_29);
lean_closure_set(x_31, 1, x_30);
lean_closure_set(x_31, 2, x_27);
x_32 = l_Lean_Elab_Command_liftCoreM___rarg(x_31, x_2, x_3, x_4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = lean_array_size(x_18);
x_37 = lean_box(0);
x_38 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4(x_18, x_33, x_35, x_18, x_36, x_14, x_37, x_2, x_3, x_34);
lean_dec(x_18);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
return x_32;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_32, 0);
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_32);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__3(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4(x_1, x_2, x_3, x_4, x_11, x_12, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabDeriving", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_elabDeriving___closed__1;
x_2 = l_Lean_Elab_applyDerivingHandlers___closed__1;
x_3 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving__1___closed__4() {
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
x_2 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__3;
x_3 = l_Lean_Elab_elabDeriving___closed__5;
x_4 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__4;
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
x_2 = l___regBuiltin_Lean_Elab_elabDeriving__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_elabDeriving_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_3, x_5);
x_13 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_12);
x_14 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_12, x_13, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_array_push(x_6, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_5, x_19);
x_5 = x_20;
x_6 = x_18;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_10, x_15);
lean_dec(x_10);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_lt(x_9, x_18);
x_20 = 0;
if (x_19 == 0)
{
lean_object* x_38; 
lean_dec(x_18);
lean_dec(x_17);
x_38 = l_Lean_Elab_elabDeriving___closed__6;
x_21 = x_38;
goto block_37;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_18, x_18);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_18);
lean_dec(x_17);
x_40 = l_Lean_Elab_elabDeriving___closed__6;
x_21 = x_40;
goto block_37;
}
else
{
size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_42 = l_Lean_Elab_elabDeriving___closed__7;
x_43 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_17, x_20, x_41, x_42);
lean_dec(x_17);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_21 = x_44;
goto block_37;
}
}
block_37:
{
size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_array_size(x_21);
x_23 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__2(x_22, x_20, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = lean_array_size(x_24);
x_27 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1;
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(x_24, x_25, x_24, x_26, x_20, x_27, x_2, x_3, x_4);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
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
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
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
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DerivingClassView_applyHandlers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_replaceRef(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 6);
lean_dec(x_13);
lean_ctor_set(x_3, 6, x_11);
x_14 = l_Lean_Elab_applyDerivingHandlers(x_7, x_2, x_3, x_4, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
x_19 = lean_ctor_get(x_3, 4);
x_20 = lean_ctor_get(x_3, 5);
x_21 = lean_ctor_get(x_3, 7);
x_22 = lean_ctor_get(x_3, 8);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_18);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_11);
lean_ctor_set(x_24, 7, x_21);
lean_ctor_set(x_24, 8, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*9, x_23);
x_25 = l_Lean_Elab_applyDerivingHandlers(x_7, x_2, x_24, x_4, x_10);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_elabDeriving___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__1;
x_2 = l_Lean_Elab_applyDerivingHandlers___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__2;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__4;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__6;
x_2 = l_Lean_Elab_elabDeriving___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__7;
x_2 = l_Lean_Elab_applyDerivingHandlers___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__8;
x_2 = l_Lean_Elab_applyDerivingHandlers___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Basic", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__9;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__11;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__13;
x_2 = lean_unsigned_to_nat(1937u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_applyDerivingHandlers___closed__3;
x_3 = 0;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__14;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1 = _init_l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_Term_mkInst_x3f___closed__1);
l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__1);
l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__2);
l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__3 = _init_l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__3);
l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__4 = _init_l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Elab_Term_processDefDeriving___spec__1___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_processDefDeriving___spec__6___closed__6);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_processDefDeriving___spec__7___rarg___closed__2);
l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__1 = _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__1();
lean_mark_persistent(l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__1);
l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__2 = _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__2();
lean_mark_persistent(l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__2);
l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__3 = _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__3();
lean_mark_persistent(l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__3);
l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__4 = _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__4();
lean_mark_persistent(l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__4);
l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__5 = _init_l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__5();
lean_mark_persistent(l_Lean_addDeclarationRanges___at_Lean_Elab_Term_processDefDeriving___spec__10___closed__5);
l_Lean_Elab_Term_processDefDeriving___closed__1 = _init_l_Lean_Elab_Term_processDefDeriving___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_processDefDeriving___closed__1);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_652_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_derivingHandlersRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_derivingHandlersRef);
lean_dec_ref(res);
}l_Lean_Elab_registerDerivingHandler___lambda__1___closed__1 = _init_l_Lean_Elab_registerDerivingHandler___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_registerDerivingHandler___lambda__1___closed__1);
l_Lean_Elab_registerDerivingHandler___closed__1 = _init_l_Lean_Elab_registerDerivingHandler___closed__1();
lean_mark_persistent(l_Lean_Elab_registerDerivingHandler___closed__1);
l_Lean_Elab_registerDerivingHandler___closed__2 = _init_l_Lean_Elab_registerDerivingHandler___closed__2();
lean_mark_persistent(l_Lean_Elab_registerDerivingHandler___closed__2);
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
l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__1);
l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_applyDerivingHandlers___spec__1___closed__2);
l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__1 = _init_l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__1);
l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__2 = _init_l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_applyDerivingHandlers___lambda__1___closed__2);
l_Lean_Elab_applyDerivingHandlers___lambda__3___closed__1 = _init_l_Lean_Elab_applyDerivingHandlers___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_applyDerivingHandlers___lambda__3___closed__1);
l_Lean_Elab_applyDerivingHandlers___closed__1 = _init_l_Lean_Elab_applyDerivingHandlers___closed__1();
lean_mark_persistent(l_Lean_Elab_applyDerivingHandlers___closed__1);
l_Lean_Elab_applyDerivingHandlers___closed__2 = _init_l_Lean_Elab_applyDerivingHandlers___closed__2();
lean_mark_persistent(l_Lean_Elab_applyDerivingHandlers___closed__2);
l_Lean_Elab_applyDerivingHandlers___closed__3 = _init_l_Lean_Elab_applyDerivingHandlers___closed__3();
lean_mark_persistent(l_Lean_Elab_applyDerivingHandlers___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_elabDeriving___spec__4___closed__1);
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
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__8);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__9 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__9();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__9);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__10 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__10();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__10);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__11 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__11();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__11);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__12 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__12();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__12);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__13 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__13();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__13);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__14 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__14();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937____closed__14);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1937_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
