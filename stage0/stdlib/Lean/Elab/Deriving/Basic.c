// Lean compiler output
// Module: Lean.Elab.Deriving.Basic
// Imports: Init Lean.Elab.Command Lean.Elab.MutualDef
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_derivingHandlersRef;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(lean_object*);
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__1;
static lean_object* l_Lean_Elab_defaultHandler___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__3;
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getOptDerivingClasses(lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1;
static lean_object* l_Lean_Elab_elabDeriving___lambda__2___closed__1;
static lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__1;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getOptDerivingClasses___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__7;
static lean_object* l_Lean_Elab_defaultHandler___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__3;
static lean_object* l_Lean_Elab_elabDeriving___lambda__2___closed__2;
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__2;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__3;
static lean_object* l_Lean_Elab_elabDeriving___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__2;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_21_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___boxed__const__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_defaultHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__1;
static lean_object* l_Lean_Elab_defaultHandler___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__1;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_elabDeriving___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__8;
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg___closed__1;
static lean_object* l_Lean_Elab_elabDeriving___closed__4;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__1;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__9;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2;
static lean_object* l_Lean_Elab_elabDeriving___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_DerivingClassView_applyHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_MkInstanceName_main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getOptDerivingClasses___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_elabDeriving___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(size_t, size_t, lean_object*);
lean_object* l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_6598____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__18(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_defaultHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_processDefDeriving(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving___lambda__2(lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeriving(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__2;
static lean_object* l_Lean_Elab_elabDeriving___closed__11;
lean_object* lean_io_initializing(lean_object*);
static lean_object* l_Lean_Elab_getOptDerivingClasses___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_elabDeriving___closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_elabDeriving(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__2;
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__17(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getOptDerivingClasses___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__2;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_21_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_IO_mkRef___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_Lean_Elab_derivingHandlersRef;
x_6 = lean_st_ref_take(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_1, x_2);
x_10 = lean_st_ref_set(x_5, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to register deriving handler, a handler has already been registered for '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_5 = l_Lean_Elab_derivingHandlersRef;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_NameMap_contains___rarg(x_8, x_1);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_6);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1(x_1, x_2, x_11, x_9);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_13 = 1;
x_14 = l_Lean_Name_toString(x_1, x_13);
x_15 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = l_Lean_NameMap_contains___rarg(x_20, x_1);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1(x_1, x_2, x_23, x_21);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_25 = 1;
x_26 = l_Lean_Name_toString(x_1, x_25);
x_27 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to register deriving handler, it can only be registered during initialization");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_initializing(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
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
x_9 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__2;
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
x_11 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__2;
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
x_15 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2(x_1, x_2, x_14, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_defaultHandler___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("default handlers have not been implemented yet, class: '");
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
x_1 = lean_mk_string("' types: ");
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
x_1 = lean_mk_string("");
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
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_Elab_defaultHandler___closed__2;
x_8 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Elab_defaultHandler___closed__4;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_to_list(lean_box(0), x_2);
x_12 = lean_box(0);
x_13 = l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(x_11, x_12);
x_14 = l_Lean_MessageData_ofList(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_defaultHandler___closed__6;
x_17 = lean_alloc_ctor(10, 2, 0);
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
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyDerivingHandlers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Elab_derivingHandlersRef;
x_8 = lean_st_ref_get(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1(x_9, x_1);
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
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_14 = lean_apply_5(x_13, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Elab_defaultHandler(x_1, x_2, x_4, x_5, x_17);
lean_dec(x_5);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Term_processDefDeriving), 9, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = l_Lean_Elab_Command_liftTermElabM___rarg(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg___closed__1;
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
static lean_object* _init_l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = 1;
x_11 = x_2 + x_10;
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = x_12;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_11;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = 1;
x_11 = x_2 + x_10;
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = x_12;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_11;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_elabDeriving___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__12(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_9);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__12(x_2, x_19, x_4, x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_8, x_12, x_16, x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_ResolveName_resolveGlobalName(x_8, x_12, x_20, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown constant '");
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = l_Lean_mkConst(x_1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__3;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__11(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_List_filterAux___at_Lean_resolveGlobalConstCore___spec__1(x_6, x_8);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10___lambda__1(x_9, x_8, x_11, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_9);
x_13 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12(x_1, x_2, x_3, x_7);
lean_dec(x_3);
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
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected identifier");
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(x_6);
x_8 = l_List_isEmpty___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 6);
lean_dec(x_15);
lean_ctor_set(x_2, 6, x_13);
x_16 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10(x_5, x_2, x_3, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set(x_23, 6, x_13);
x_24 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10(x_5, x_23, x_3, x_12);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__3;
x_26 = l_Lean_throwErrorAt___at_Lean_Elab_elabDeriving___spec__9(x_1, x_25, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_26;
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous identifier '");
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', possible interpretations: ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_11 = l_Lean_Syntax_formatStxAux(x_8, x_9, x_10, x_1);
x_12 = l_Std_Format_defWidth;
x_13 = lean_format_pretty(x_11, x_12);
x_14 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(x_6, x_18);
x_20 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_19);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
x_22 = l_Lean_Elab_defaultHandler___closed__5;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_throwErrorAt___at_Lean_Elab_Command_MkInstanceName_main___spec__6(x_1, x_25, x_2, x_3, x_7);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_30);
return x_5;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = 0;
x_37 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_38 = l_Lean_Syntax_formatStxAux(x_35, x_36, x_37, x_1);
x_39 = l_Std_Format_defWidth;
x_40 = lean_format_pretty(x_38, x_39);
x_41 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_box(0);
x_46 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(x_6, x_45);
x_47 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_46);
x_48 = lean_string_append(x_44, x_47);
lean_dec(x_47);
x_49 = l_Lean_Elab_defaultHandler___closed__5;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_throwErrorAt___at_Lean_Elab_Command_MkInstanceName_main___spec__6(x_1, x_52, x_2, x_3, x_34);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
return x_5;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = lean_environment_find(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_5);
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_1, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__15(x_17, x_2, x_3, x_8);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = lean_environment_find(x_22, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_box(0);
x_25 = l_Lean_mkConst(x_1, x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__15(x_30, x_2, x_3, x_21);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__14(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_ConstantInfo_levelParams(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_8, x_9);
x_11 = l_Lean_mkConst(x_1, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = l_Lean_ConstantInfo_levelParams(x_12);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_14, x_15);
x_17 = l_Lean_mkConst(x_1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 7);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_18, 1);
x_24 = l_Std_PersistentArray_push___rarg(x_23, x_1);
lean_ctor_set(x_18, 1, x_24);
x_25 = lean_st_ref_set(x_3, x_17, x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = l_Std_PersistentArray_push___rarg(x_34, x_1);
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_32);
lean_ctor_set(x_17, 7, x_36);
x_37 = lean_st_ref_set(x_3, x_17, x_19);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
x_44 = lean_ctor_get(x_17, 2);
x_45 = lean_ctor_get(x_17, 3);
x_46 = lean_ctor_get(x_17, 4);
x_47 = lean_ctor_get(x_17, 5);
x_48 = lean_ctor_get(x_17, 6);
x_49 = lean_ctor_get(x_17, 8);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_50 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
x_51 = lean_ctor_get(x_18, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_53 = x_18;
} else {
 lean_dec_ref(x_18);
 x_53 = lean_box(0);
}
x_54 = l_Std_PersistentArray_push___rarg(x_52, x_1);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 1);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_50);
x_56 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_44);
lean_ctor_set(x_56, 3, x_45);
lean_ctor_set(x_56, 4, x_46);
lean_ctor_set(x_56, 5, x_47);
lean_ctor_set(x_56, 6, x_48);
lean_ctor_set(x_56, 7, x_55);
lean_ctor_set(x_56, 8, x_49);
x_57 = lean_st_ref_set(x_3, x_56, x_19);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__2;
x_3 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__17(x_17, x_2, x_3, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 7);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
lean_inc(x_3);
lean_inc(x_7);
x_18 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__13(x_7, x_3, x_4, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
x_23 = l_Lean_LocalContext_empty;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_2);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16(x_26, x_3, x_4, x_20);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_7);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_6);
if (x_36 == 0)
{
return x_6;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__18(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_2 < x_1;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_uget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = x_10;
x_14 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_13, x_14, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_2 + x_18;
x_20 = x_16;
x_21 = lean_array_uset(x_12, x_2, x_20);
x_2 = x_19;
x_3 = x_21;
x_6 = x_17;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_applyDerivingHandlers(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_4 < x_3;
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
lean_object* x_11; lean_object* x_12; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_11 = lean_array_uget(x_2, x_4);
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 2);
lean_inc(x_32);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_11);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
x_12 = x_35;
goto block_29;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_55; lean_object* x_56; 
x_37 = lean_ctor_get(x_5, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_5, 0);
lean_dec(x_39);
x_40 = lean_array_fget(x_30, x_31);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_31, x_41);
lean_dec(x_31);
lean_ctor_set(x_5, 1, x_42);
x_55 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_11);
x_56 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_11, x_55, x_6, x_7, x_8);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_get_size(x_1);
x_60 = lean_nat_dec_eq(x_59, x_41);
lean_dec(x_59);
x_61 = l_Lean_Elab_Command_getRef(x_6, x_7, x_58);
if (x_60 == 0)
{
lean_object* x_78; 
x_78 = lean_box(0);
x_62 = x_78;
goto block_77;
}
else
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = lean_ctor_get(x_61, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
lean_dec(x_61);
x_81 = l_Lean_replaceRef(x_11, x_79);
lean_dec(x_79);
lean_dec(x_11);
x_82 = lean_ctor_get(x_6, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_6, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_6, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_6, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_6, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_6, 5);
lean_inc(x_87);
x_88 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_83);
lean_ctor_set(x_88, 2, x_84);
lean_ctor_set(x_88, 3, x_85);
lean_ctor_set(x_88, 4, x_86);
lean_ctor_set(x_88, 5, x_87);
lean_ctor_set(x_88, 6, x_81);
x_89 = l_Lean_instInhabitedName;
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_array_get(x_89, x_1, x_90);
lean_inc(x_88);
lean_inc(x_57);
x_92 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(x_57, x_91, x_88, x_7, x_80);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
lean_inc(x_7);
lean_inc(x_1);
x_96 = l_Lean_Elab_applyDerivingHandlers(x_57, x_1, x_40, x_88, x_7, x_95);
if (lean_obj_tag(x_96) == 0)
{
x_43 = x_96;
goto block_54;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_7);
lean_inc(x_6);
x_99 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_97, x_6, x_7, x_98);
x_43 = x_99;
goto block_54;
}
}
else
{
uint8_t x_100; 
lean_dec(x_88);
lean_dec(x_57);
x_100 = !lean_is_exclusive(x_92);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_92, 0);
lean_dec(x_101);
x_102 = lean_box(0);
lean_ctor_set(x_92, 0, x_102);
x_43 = x_92;
goto block_54;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_92, 1);
lean_inc(x_103);
lean_dec(x_92);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_43 = x_105;
goto block_54;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_88);
lean_dec(x_57);
x_106 = lean_ctor_get(x_92, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_92, 1);
lean_inc(x_107);
lean_dec(x_92);
lean_inc(x_7);
lean_inc(x_6);
x_108 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_106, x_6, x_7, x_107);
x_43 = x_108;
goto block_54;
}
}
else
{
lean_object* x_109; 
x_109 = lean_box(0);
x_62 = x_109;
goto block_77;
}
}
block_77:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_62);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Lean_replaceRef(x_11, x_63);
lean_dec(x_63);
lean_dec(x_11);
x_66 = lean_ctor_get(x_6, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_6, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_6, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_6, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_6, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_6, 5);
lean_inc(x_71);
x_72 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_67);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_69);
lean_ctor_set(x_72, 4, x_70);
lean_ctor_set(x_72, 5, x_71);
lean_ctor_set(x_72, 6, x_65);
lean_inc(x_7);
lean_inc(x_1);
x_73 = l_Lean_Elab_applyDerivingHandlers(x_57, x_1, x_40, x_72, x_7, x_64);
if (lean_obj_tag(x_73) == 0)
{
x_43 = x_73;
goto block_54;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_7);
lean_inc(x_6);
x_76 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_74, x_6, x_7, x_75);
x_43 = x_76;
goto block_54;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_40);
lean_dec(x_11);
x_110 = lean_ctor_get(x_56, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_56, 1);
lean_inc(x_111);
lean_dec(x_56);
lean_inc(x_7);
lean_inc(x_6);
x_112 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_110, x_6, x_7, x_111);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
lean_dec(x_114);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_5);
lean_ctor_set(x_112, 0, x_115);
x_12 = x_112;
goto block_29;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_5);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_12 = x_118;
goto block_29;
}
}
else
{
uint8_t x_119; 
lean_dec(x_5);
x_119 = !lean_is_exclusive(x_112);
if (x_119 == 0)
{
x_12 = x_112;
goto block_29;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_112, 0);
x_121 = lean_ctor_get(x_112, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_112);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_12 = x_122;
goto block_29;
}
}
}
block_54:
{
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_43, 0, x_46);
x_12 = x_43;
goto block_29;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_5);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_12 = x_49;
goto block_29;
}
}
else
{
uint8_t x_50; 
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
x_12 = x_43;
goto block_29;
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
x_12 = x_53;
goto block_29;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_137; lean_object* x_138; 
lean_dec(x_5);
x_123 = lean_array_fget(x_30, x_31);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_add(x_31, x_124);
lean_dec(x_31);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_30);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_32);
x_137 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_11);
x_138 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_11, x_137, x_6, x_7, x_8);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_array_get_size(x_1);
x_142 = lean_nat_dec_eq(x_141, x_124);
lean_dec(x_141);
x_143 = l_Lean_Elab_Command_getRef(x_6, x_7, x_140);
if (x_142 == 0)
{
lean_object* x_160; 
x_160 = lean_box(0);
x_144 = x_160;
goto block_159;
}
else
{
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_161 = lean_ctor_get(x_143, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_143, 1);
lean_inc(x_162);
lean_dec(x_143);
x_163 = l_Lean_replaceRef(x_11, x_161);
lean_dec(x_161);
lean_dec(x_11);
x_164 = lean_ctor_get(x_6, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_6, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_6, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_6, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_6, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_6, 5);
lean_inc(x_169);
x_170 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_170, 0, x_164);
lean_ctor_set(x_170, 1, x_165);
lean_ctor_set(x_170, 2, x_166);
lean_ctor_set(x_170, 3, x_167);
lean_ctor_set(x_170, 4, x_168);
lean_ctor_set(x_170, 5, x_169);
lean_ctor_set(x_170, 6, x_163);
x_171 = l_Lean_instInhabitedName;
x_172 = lean_unsigned_to_nat(0u);
x_173 = lean_array_get(x_171, x_1, x_172);
lean_inc(x_170);
lean_inc(x_139);
x_174 = l___private_Lean_Elab_Deriving_Basic_0__Lean_Elab_tryApplyDefHandler(x_139, x_173, x_170, x_7, x_162);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
lean_inc(x_7);
lean_inc(x_1);
x_178 = l_Lean_Elab_applyDerivingHandlers(x_139, x_1, x_123, x_170, x_7, x_177);
if (lean_obj_tag(x_178) == 0)
{
x_127 = x_178;
goto block_136;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
lean_inc(x_7);
lean_inc(x_6);
x_181 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_179, x_6, x_7, x_180);
x_127 = x_181;
goto block_136;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_170);
lean_dec(x_139);
x_182 = lean_ctor_get(x_174, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_183 = x_174;
} else {
 lean_dec_ref(x_174);
 x_183 = lean_box(0);
}
x_184 = lean_box(0);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
x_127 = x_185;
goto block_136;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_170);
lean_dec(x_139);
x_186 = lean_ctor_get(x_174, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_174, 1);
lean_inc(x_187);
lean_dec(x_174);
lean_inc(x_7);
lean_inc(x_6);
x_188 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_186, x_6, x_7, x_187);
x_127 = x_188;
goto block_136;
}
}
else
{
lean_object* x_189; 
x_189 = lean_box(0);
x_144 = x_189;
goto block_159;
}
}
block_159:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_144);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = l_Lean_replaceRef(x_11, x_145);
lean_dec(x_145);
lean_dec(x_11);
x_148 = lean_ctor_get(x_6, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_6, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_6, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_6, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_6, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_6, 5);
lean_inc(x_153);
x_154 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_149);
lean_ctor_set(x_154, 2, x_150);
lean_ctor_set(x_154, 3, x_151);
lean_ctor_set(x_154, 4, x_152);
lean_ctor_set(x_154, 5, x_153);
lean_ctor_set(x_154, 6, x_147);
lean_inc(x_7);
lean_inc(x_1);
x_155 = l_Lean_Elab_applyDerivingHandlers(x_139, x_1, x_123, x_154, x_7, x_146);
if (lean_obj_tag(x_155) == 0)
{
x_127 = x_155;
goto block_136;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_7);
lean_inc(x_6);
x_158 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_156, x_6, x_7, x_157);
x_127 = x_158;
goto block_136;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_123);
lean_dec(x_11);
x_190 = lean_ctor_get(x_138, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_138, 1);
lean_inc(x_191);
lean_dec(x_138);
lean_inc(x_7);
lean_inc(x_6);
x_192 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_190, x_6, x_7, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_126);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_193);
x_12 = x_196;
goto block_29;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_126);
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_199 = x_192;
} else {
 lean_dec_ref(x_192);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
x_12 = x_200;
goto block_29;
}
}
block_136:
{
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_126);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
x_12 = x_131;
goto block_29;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_126);
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_134 = x_127;
} else {
 lean_dec_ref(x_127);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
x_12 = x_135;
goto block_29;
}
}
}
}
block_29:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = 1;
x_23 = x_4 + x_22;
x_4 = x_23;
x_5 = x_21;
x_8 = x_20;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
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
x_1 = lean_mk_string("group");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_elabDeriving___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_nullKind;
x_11 = lean_unsigned_to_nat(2u);
lean_inc(x_8);
x_12 = l_Lean_Syntax_isNodeOf(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_6);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Syntax_getArg(x_8, x_7);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_elabDeriving___lambda__1(x_6, x_16, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_elabDeriving___lambda__1(x_6, x_19, x_18);
return x_20;
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
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_elabDeriving___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabDeriving___closed__2;
x_2 = l_Lean_Elab_elabDeriving___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabDeriving___closed__4;
x_2 = l_Lean_Elab_elabDeriving___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("deriving");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabDeriving___closed__6;
x_2 = l_Lean_Elab_elabDeriving___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeriving___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabDeriving___closed__11() {
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
x_5 = l_Lean_Elab_elabDeriving___closed__8;
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
lean_object* x_75; 
lean_dec(x_11);
lean_dec(x_10);
x_75 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_14 = x_75;
goto block_74;
}
else
{
uint8_t x_76; 
x_76 = lean_nat_dec_le(x_11, x_11);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_11);
lean_dec(x_10);
x_77 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_14 = x_77;
goto block_74;
}
else
{
size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = 0;
x_79 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_80 = l_Lean_Elab_elabDeriving___closed__9;
x_81 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_10, x_78, x_79, x_80);
lean_dec(x_10);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_14 = x_82;
goto block_74;
}
}
block_74:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Elab_elabDeriving___closed__10;
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
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = x_18;
lean_inc(x_22);
x_23 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(x_20, x_21, x_22);
x_24 = x_23;
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(x_20, x_21, x_22);
x_26 = x_25;
x_27 = lean_unsigned_to_nat(4u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
lean_dec(x_1);
x_29 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_12, x_30);
if (x_31 == 0)
{
lean_object* x_67; 
lean_dec(x_30);
lean_dec(x_29);
x_67 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_32 = x_67;
goto block_66;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_30, x_30);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_30);
lean_dec(x_29);
x_69 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_32 = x_69;
goto block_66;
}
else
{
size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_71 = l_Lean_Elab_elabDeriving___closed__9;
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_29, x_21, x_70, x_71);
lean_dec(x_29);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_32 = x_73;
goto block_66;
}
}
block_66:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Elab_elabDeriving___closed__11;
x_34 = l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_6598____spec__1(x_32, x_33);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_35 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(x_4);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_array_get_size(x_36);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = x_36;
x_40 = lean_box_usize(x_38);
x_41 = l_Lean_Elab_elabDeriving___boxed__const__1;
x_42 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__18___boxed), 6, 3);
lean_closure_set(x_42, 0, x_40);
lean_closure_set(x_42, 1, x_41);
lean_closure_set(x_42, 2, x_39);
x_43 = x_42;
lean_inc(x_3);
lean_inc(x_2);
x_44 = lean_apply_3(x_43, x_2, x_3, x_4);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_get_size(x_24);
x_48 = l_Array_toSubarray___rarg(x_24, x_12, x_47);
x_49 = lean_array_get_size(x_26);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19(x_45, x_26, x_50, x_21, x_48, x_2, x_3, x_46);
lean_dec(x_26);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_44);
if (x_62 == 0)
{
return x_44;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_44, 0);
x_64 = lean_ctor_get(x_44, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_44);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_elabDeriving___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_elabDeriving___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__11(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_elabDeriving___spec__10___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__15(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__14(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__17(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__18(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__19(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabDeriving___closed__2;
x_2 = l___regBuiltin_Lean_Elab_elabDeriving___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabDeriving");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_elabDeriving___closed__2;
x_2 = l___regBuiltin_Lean_Elab_elabDeriving___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeriving), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_elabDeriving(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Elab_elabDeriving___closed__8;
x_4 = l___regBuiltin_Lean_Elab_elabDeriving___closed__4;
x_5 = l___regBuiltin_Lean_Elab_elabDeriving___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = x_2 + x_16;
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_2);
x_9 = lean_array_push(x_3, x_8);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
x_14 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_9 < x_8;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
x_25 = lean_box_usize(x_9);
x_26 = lean_box_usize(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_2);
lean_closure_set(x_27, 3, x_3);
lean_closure_set(x_27, 4, x_4);
lean_closure_set(x_27, 5, x_5);
lean_closure_set(x_27, 6, x_6);
lean_closure_set(x_27, 7, x_7);
lean_closure_set(x_27, 8, x_26);
if (x_24 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_10);
x_31 = lean_apply_2(x_29, lean_box(0), x_30);
x_32 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_31, x_27);
return x_32;
}
else
{
uint8_t x_33; 
lean_free_object(x_10);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_16, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_16, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_16, 0);
lean_dec(x_36);
x_37 = lean_array_fget(x_21, x_22);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_22, x_38);
lean_dec(x_22);
lean_ctor_set(x_16, 1, x_39);
x_40 = lean_box(0);
lean_inc(x_15);
lean_inc(x_1);
x_41 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___rarg(x_1, x_5, x_3, x_2, x_4, x_15, x_40);
lean_inc(x_6);
x_42 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3), 7, 6);
lean_closure_set(x_42, 0, x_15);
lean_closure_set(x_42, 1, x_37);
lean_closure_set(x_42, 2, x_19);
lean_closure_set(x_42, 3, x_1);
lean_closure_set(x_42, 4, x_16);
lean_closure_set(x_42, 5, x_6);
x_43 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_41, x_42);
x_44 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_43, x_27);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_16);
x_45 = lean_array_fget(x_21, x_22);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_22, x_46);
lean_dec(x_22);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_23);
x_49 = lean_box(0);
lean_inc(x_15);
lean_inc(x_1);
x_50 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___rarg(x_1, x_5, x_3, x_2, x_4, x_15, x_49);
lean_inc(x_6);
x_51 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3), 7, 6);
lean_closure_set(x_51, 0, x_15);
lean_closure_set(x_51, 1, x_45);
lean_closure_set(x_51, 2, x_19);
lean_closure_set(x_51, 3, x_1);
lean_closure_set(x_51, 4, x_48);
lean_closure_set(x_51, 5, x_6);
x_52 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_50, x_51);
x_53 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_52, x_27);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_10, 1);
lean_inc(x_54);
lean_dec(x_10);
x_55 = lean_ctor_get(x_16, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_16, 2);
lean_inc(x_57);
x_58 = lean_nat_dec_lt(x_56, x_57);
x_59 = lean_box_usize(x_9);
x_60 = lean_box_usize(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_61 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_61, 0, x_1);
lean_closure_set(x_61, 1, x_59);
lean_closure_set(x_61, 2, x_2);
lean_closure_set(x_61, 3, x_3);
lean_closure_set(x_61, 4, x_4);
lean_closure_set(x_61, 5, x_5);
lean_closure_set(x_61, 6, x_6);
lean_closure_set(x_61, 7, x_7);
lean_closure_set(x_61, 8, x_60);
if (x_58 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
lean_dec(x_1);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_16);
lean_ctor_set(x_64, 1, x_54);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_apply_2(x_63, lean_box(0), x_65);
x_67 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_66, x_61);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_68 = x_16;
} else {
 lean_dec_ref(x_16);
 x_68 = lean_box(0);
}
x_69 = lean_array_fget(x_55, x_56);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_56, x_70);
lean_dec(x_56);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 3, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_55);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_57);
x_73 = lean_box(0);
lean_inc(x_15);
lean_inc(x_1);
x_74 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___rarg(x_1, x_5, x_3, x_2, x_4, x_15, x_73);
lean_inc(x_6);
x_75 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3), 7, 6);
lean_closure_set(x_75, 0, x_15);
lean_closure_set(x_75, 1, x_69);
lean_closure_set(x_75, 2, x_54);
lean_closure_set(x_75, 3, x_1);
lean_closure_set(x_75, 4, x_72);
lean_closure_set(x_75, 5, x_6);
x_76 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_74, x_75);
x_77 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_76, x_61);
return x_77;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getOptDerivingClasses___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optDeriving");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getOptDerivingClasses___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabDeriving___closed__6;
x_2 = l_Lean_Elab_getOptDerivingClasses___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getOptDerivingClasses___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Elab_getOptDerivingClasses___rarg___closed__2;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_6, x_13);
lean_dec(x_6);
x_15 = l_Lean_nullKind;
x_16 = lean_unsigned_to_nat(2u);
lean_inc(x_14);
x_17 = l_Lean_Syntax_isNodeOf(x_14, x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_14, x_22);
lean_dec(x_14);
x_24 = l_Lean_Syntax_getArgs(x_23);
lean_dec(x_23);
x_25 = lean_array_get_size(x_24);
x_26 = lean_nat_dec_lt(x_13, x_25);
if (x_26 == 0)
{
lean_object* x_54; 
lean_dec(x_25);
lean_dec(x_24);
x_54 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_27 = x_54;
goto block_53;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_25, x_25);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_25);
lean_dec(x_24);
x_56 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_27 = x_56;
goto block_53;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_59 = l_Lean_Elab_elabDeriving___closed__9;
x_60 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_24, x_57, x_58, x_59);
lean_dec(x_24);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_27 = x_61;
goto block_53;
}
}
block_53:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Elab_elabDeriving___closed__10;
x_29 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(x_27, x_28);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_33 = lean_apply_2(x_31, lean_box(0), x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = x_34;
lean_inc(x_38);
x_39 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(x_36, x_37, x_38);
x_40 = x_39;
x_41 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(x_36, x_37, x_38);
x_42 = x_41;
x_43 = lean_array_get_size(x_40);
x_44 = l_Array_toSubarray___rarg(x_40, x_13, x_43);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_array_get_size(x_42);
x_49 = lean_usize_of_nat(x_48);
lean_dec(x_48);
lean_inc(x_45);
lean_inc(x_1);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_45, x_42, x_49, x_37, x_47);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_getOptDerivingClasses___rarg___lambda__1), 2, 1);
lean_closure_set(x_51, 0, x_1);
x_52 = lean_apply_4(x_45, lean_box(0), lean_box(0), x_50, x_51);
return x_52;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getOptDerivingClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getOptDerivingClasses___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get(x_3, 3);
x_20 = lean_ctor_get(x_3, 4);
x_21 = lean_ctor_get(x_3, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_22, 6, x_12);
x_23 = l_Lean_Elab_applyDerivingHandlers(x_7, x_2, x_8, x_22, x_4, x_11);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_elabDeriving___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Deriving");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__3;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_MutualDef(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MutualDef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_21_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_derivingHandlersRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_derivingHandlersRef);
lean_dec_ref(res);
l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__1 = _init_l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__1);
l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2 = _init_l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2);
l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__1 = _init_l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__1();
lean_mark_persistent(l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__1);
l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__2 = _init_l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__2();
lean_mark_persistent(l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__2);
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
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg___closed__1);
l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1 = _init_l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1();
lean_mark_persistent(l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__3 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__12___closed__3);
l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__1 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__1);
l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__2 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__2);
l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__3 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___closed__3);
l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1 = _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1);
l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2 = _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__1 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__1();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__1);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__2 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__2();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__2);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__3 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__3();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__16___closed__3);
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
l_Lean_Elab_elabDeriving___closed__10 = _init_l_Lean_Elab_elabDeriving___closed__10();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__10);
l_Lean_Elab_elabDeriving___closed__11 = _init_l_Lean_Elab_elabDeriving___closed__11();
lean_mark_persistent(l_Lean_Elab_elabDeriving___closed__11);
l_Lean_Elab_elabDeriving___boxed__const__1 = _init_l_Lean_Elab_elabDeriving___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_elabDeriving___boxed__const__1);
l___regBuiltin_Lean_Elab_elabDeriving___closed__1 = _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving___closed__1);
l___regBuiltin_Lean_Elab_elabDeriving___closed__2 = _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving___closed__2);
l___regBuiltin_Lean_Elab_elabDeriving___closed__3 = _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving___closed__3);
l___regBuiltin_Lean_Elab_elabDeriving___closed__4 = _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving___closed__4);
l___regBuiltin_Lean_Elab_elabDeriving___closed__5 = _init_l___regBuiltin_Lean_Elab_elabDeriving___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_elabDeriving___closed__5);
res = l___regBuiltin_Lean_Elab_elabDeriving(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_getOptDerivingClasses___rarg___closed__1 = _init_l_Lean_Elab_getOptDerivingClasses___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___rarg___closed__1);
l_Lean_Elab_getOptDerivingClasses___rarg___closed__2 = _init_l_Lean_Elab_getOptDerivingClasses___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_getOptDerivingClasses___rarg___closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299____closed__3);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1299_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
