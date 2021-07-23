// Lean compiler output
// Module: Lean.Elab.Deriving.Basic
// Imports: Init Lean.Elab.Command
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
lean_object* l_Lean_Elab_derivingHandlersRef;
size_t l_USize_add(size_t, size_t);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__2;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyDerivingHandlers_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverload___spec__2(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_elabDeriving_match__2(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__17(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__1;
static lean_object* l_Lean_Elab_defaultHandler___closed__5;
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeriving_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Elab_defaultHandler___spec__1(lean_object*);
static lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__1;
lean_object* l_Lean_Elab_getOptDerivingClasses_match__1(lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__3;
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__3;
lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_resolveGlobalConst___spec__2(lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses(lean_object*);
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1;
static lean_object* l_Lean_Elab_elabDeriving___lambda__2___closed__1;
lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeriving_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__3;
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__7;
static lean_object* l_Lean_Elab_defaultHandler___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__3;
static lean_object* l_Lean_Elab_elabDeriving___lambda__2___closed__2;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_resolveGlobalConstNoOverload___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyDerivingHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232_(lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_21_(lean_object*);
lean_object* l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeriving___boxed__const__1;
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Elab_defaultHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_defaultHandler___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__1;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___closed__2;
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__8;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg___closed__1;
static lean_object* l_Lean_Elab_elabDeriving___closed__4;
static lean_object* l_Lean_Elab_defaultHandler___closed__1;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__9;
lean_object* l_List_filterAux___at_Lean_resolveGlobalConst___spec__1(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2;
static lean_object* l_Lean_Elab_elabDeriving___closed__6;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__3;
lean_object* l_Lean_Elab_elabDeriving_match__3(lean_object*);
lean_object* l_Lean_Elab_DerivingClassView_applyHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_elabDeriving___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeriving___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__2;
lean_object* l_Lean_Elab_elabDeriving___lambda__3(lean_object*);
lean_object* l_Lean_Elab_getOptDerivingClasses___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__1;
lean_object* l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_4451____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(size_t, size_t, lean_object*);
lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___closed__1;
lean_object* l_Lean_Elab_defaultHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyDerivingHandlers_match__1(lean_object*);
lean_object* l_Lean_Elab_elabDeriving_match__4(lean_object*);
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeriving_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeriving___lambda__2(lean_object*);
lean_object* l_Lean_Elab_elabDeriving_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeriving_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_elabDeriving(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerBuiltinDerivingHandler(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__4;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabDeriving___closed__11;
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__3;
static lean_object* l_Lean_Elab_getOptDerivingClasses___rarg___closed__2;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_elabDeriving___closed__10;
lean_object* l___regBuiltin_Lean_Elab_elabDeriving(lean_object*);
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_mkConstWithLevelParams___spec__1(lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__1;
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__1;
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getOptDerivingClasses___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_elabDeriving___closed__2;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_21_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_IO_mkRef___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
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
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_4(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_registerBuiltinDerivingHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1___boxed), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_registerBuiltinDerivingHandler___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_List_map___at_Lean_Elab_defaultHandler___spec__1(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at_Lean_Elab_defaultHandler___spec__1(x_5);
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
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at_Lean_Elab_defaultHandler___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
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
lean_object* l_Lean_Elab_defaultHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
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
x_12 = l_List_map___at_Lean_Elab_defaultHandler___spec__1(x_11);
x_13 = l_Lean_MessageData_ofList(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_defaultHandler___closed__6;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_16, x_3, x_4, x_5);
return x_17;
}
}
lean_object* l_Lean_Elab_defaultHandler___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_defaultHandler(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_applyDerivingHandlers_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_applyDerivingHandlers_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_applyDerivingHandlers_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_applyDerivingHandlers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Elab_applyDerivingHandlers___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_elabDeriving_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_elabDeriving_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeriving_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabDeriving_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Elab_elabDeriving_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeriving_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabDeriving_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_elabDeriving_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeriving_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabDeriving_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_elabDeriving_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeriving_match__4___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_12);
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
lean_dec(x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown constant '");
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_registerBuiltinDerivingHandlerWithArgs___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = l_Lean_mkConst(x_1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__3;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_11, x_2, x_3, x_4);
return x_12;
}
}
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_map___at_Lean_resolveGlobalConst___spec__2(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__9(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_List_filterAux___at_Lean_resolveGlobalConst___spec__1(x_6, x_8);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___lambda__1(x_9, x_11, x_2, x_3, x_7);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_9);
x_13 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10(x_1, x_2, x_3, x_7);
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
lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_1, x_8);
x_10 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_11 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_List_map___at_Lean_resolveGlobalConstNoOverload___spec__1(x_8, x_6);
x_16 = l_List_toString___at_Lean_resolveGlobalConstNoOverload___spec__2(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = l_Lean_Elab_defaultHandler___closed__5;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__11(x_21, x_2, x_3, x_7);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_dec(x_5);
x_31 = lean_box(0);
x_32 = l_Lean_mkConst(x_1, x_31);
x_33 = lean_expr_dbg_to_string(x_32);
lean_dec(x_32);
x_34 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_List_map___at_Lean_resolveGlobalConstNoOverload___spec__1(x_31, x_6);
x_39 = l_List_toString___at_Lean_resolveGlobalConstNoOverload___spec__2(x_38);
x_40 = lean_string_append(x_37, x_39);
lean_dec(x_39);
x_41 = l_Lean_Elab_defaultHandler___closed__5;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__11(x_44, x_2, x_3, x_30);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_5);
if (x_46 == 0)
{
return x_5;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_5, 0);
x_48 = lean_ctor_get(x_5, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_5);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__14(x_17, x_2, x_3, x_8);
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
x_27 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__14(x_30, x_2, x_3, x_21);
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
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__13(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_ConstantInfo_levelParams(x_7);
lean_dec(x_7);
x_9 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_8);
x_10 = l_Lean_mkConst(x_1, x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = l_Lean_ConstantInfo_levelParams(x_11);
lean_dec(x_11);
x_14 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_13);
x_15 = l_Lean_mkConst(x_1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__2;
x_3 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__1;
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
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_16 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__16(x_17, x_2, x_3, x_15);
return x_18;
}
}
}
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 7);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_8);
x_19 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__12(x_8, x_4, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
x_24 = l_Lean_LocalContext_empty;
x_25 = 0;
x_26 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15(x_27, x_4, x_5, x_21);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_8);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
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
uint8_t x_37; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
return x_7;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__17(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_2 < x_1;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_uget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = x_10;
x_14 = l_Lean_Syntax_getId(x_13);
x_15 = lean_box(0);
lean_inc(x_4);
x_16 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_13, x_14, x_15, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = x_2 + x_19;
x_21 = x_17;
x_22 = lean_array_uset(x_12, x_2, x_21);
x_2 = x_20;
x_3 = x_22;
x_6 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_4);
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
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__18(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_33 = l_Lean_Syntax_getId(x_11);
x_34 = lean_box(0);
lean_inc(x_6);
lean_inc(x_11);
x_35 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_11, x_33, x_34, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Command_getRef(x_6, x_7, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_replaceRef(x_11, x_39);
lean_dec(x_39);
lean_dec(x_11);
x_42 = lean_ctor_get(x_6, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_6, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_6, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_6, 5);
lean_inc(x_47);
x_48 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_45);
lean_ctor_set(x_48, 4, x_46);
lean_ctor_set(x_48, 5, x_47);
lean_ctor_set(x_48, 6, x_41);
lean_inc(x_7);
lean_inc(x_1);
x_49 = l_Lean_Elab_applyDerivingHandlers(x_36, x_1, x_30, x_48, x_7, x_40);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_5);
x_12 = x_51;
x_13 = x_50;
goto block_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_52, x_6, x_7, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_5);
x_12 = x_56;
x_13 = x_55;
goto block_20;
}
else
{
uint8_t x_57; 
lean_dec(x_5);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_30);
lean_dec(x_11);
x_61 = lean_ctor_get(x_35, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec(x_35);
x_63 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_61, x_6, x_7, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_5);
x_12 = x_65;
x_13 = x_64;
goto block_20;
}
else
{
uint8_t x_66; 
lean_dec(x_5);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_5);
x_70 = lean_array_fget(x_21, x_22);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_22, x_71);
lean_dec(x_22);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_21);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_23);
x_74 = l_Lean_Syntax_getId(x_11);
x_75 = lean_box(0);
lean_inc(x_6);
lean_inc(x_11);
x_76 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_11, x_74, x_75, x_6, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Elab_Command_getRef(x_6, x_7, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_replaceRef(x_11, x_80);
lean_dec(x_80);
lean_dec(x_11);
x_83 = lean_ctor_get(x_6, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_6, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_6, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_6, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_6, 4);
lean_inc(x_87);
x_88 = lean_ctor_get(x_6, 5);
lean_inc(x_88);
x_89 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_89, 2, x_85);
lean_ctor_set(x_89, 3, x_86);
lean_ctor_set(x_89, 4, x_87);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set(x_89, 6, x_82);
lean_inc(x_7);
lean_inc(x_1);
x_90 = l_Lean_Elab_applyDerivingHandlers(x_77, x_1, x_70, x_89, x_7, x_81);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_73);
x_12 = x_92;
x_13 = x_91;
goto block_20;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_93, x_6, x_7, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_73);
x_12 = x_97;
x_13 = x_96;
goto block_20;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_100 = x_95;
} else {
 lean_dec_ref(x_95);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_70);
lean_dec(x_11);
x_102 = lean_ctor_get(x_76, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_76, 1);
lean_inc(x_103);
lean_dec(x_76);
x_104 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_102, x_6, x_7, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_73);
x_12 = x_106;
x_13 = x_105;
goto block_20;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_109 = x_104;
} else {
 lean_dec_ref(x_104);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
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
x_18 = x_4 + x_17;
x_4 = x_18;
x_5 = x_16;
x_8 = x_13;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_elabDeriving___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_elabDeriving___lambda__2(lean_object* x_1) {
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
lean_object* l_Lean_Elab_elabDeriving___lambda__3(lean_object* x_1) {
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
lean_object* l_Lean_Elab_elabDeriving(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_34 = l_Array_sequenceMap___at_myMacro____x40_Init_NotationExtra___hyg_4451____spec__1(x_32, x_33);
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
x_42 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__17___boxed), 6, 3);
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
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__18(x_45, x_26, x_50, x_21, x_48, x_2, x_3, x_46);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_elabDeriving___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_sequenceMap_loop___at_Lean_Elab_elabDeriving___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_sequenceMap___at_Lean_Elab_elabDeriving___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalName___at_Lean_Elab_elabDeriving___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalConst___at_Lean_Elab_elabDeriving___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__11(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_elabDeriving___spec__14(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at_Lean_Elab_elabDeriving___spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_elabDeriving___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_elabDeriving___spec__16(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_elabDeriving___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_elabDeriving___spec__17(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_elabDeriving___spec__18(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_elabDeriving___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___regBuiltin_Lean_Elab_elabDeriving(lean_object* x_1) {
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
lean_object* l_Lean_Elab_getOptDerivingClasses_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_getOptDerivingClasses_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getOptDerivingClasses_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_40 = l_Lean_Syntax_getId(x_15);
x_41 = lean_box(0);
lean_inc(x_15);
lean_inc(x_1);
x_42 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___rarg(x_1, x_5, x_3, x_2, x_4, x_15, x_40, x_41);
lean_inc(x_6);
x_43 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3), 7, 6);
lean_closure_set(x_43, 0, x_15);
lean_closure_set(x_43, 1, x_37);
lean_closure_set(x_43, 2, x_19);
lean_closure_set(x_43, 3, x_1);
lean_closure_set(x_43, 4, x_16);
lean_closure_set(x_43, 5, x_6);
x_44 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_42, x_43);
x_45 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_44, x_27);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_16);
x_46 = lean_array_fget(x_21, x_22);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_22, x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_21);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_23);
x_50 = l_Lean_Syntax_getId(x_15);
x_51 = lean_box(0);
lean_inc(x_15);
lean_inc(x_1);
x_52 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___rarg(x_1, x_5, x_3, x_2, x_4, x_15, x_50, x_51);
lean_inc(x_6);
x_53 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3), 7, 6);
lean_closure_set(x_53, 0, x_15);
lean_closure_set(x_53, 1, x_46);
lean_closure_set(x_53, 2, x_19);
lean_closure_set(x_53, 3, x_1);
lean_closure_set(x_53, 4, x_49);
lean_closure_set(x_53, 5, x_6);
x_54 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_52, x_53);
x_55 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_54, x_27);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_dec(x_10);
x_57 = lean_ctor_get(x_16, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_16, 2);
lean_inc(x_59);
x_60 = lean_nat_dec_lt(x_58, x_59);
x_61 = lean_box_usize(x_9);
x_62 = lean_box_usize(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_63 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1___boxed), 10, 9);
lean_closure_set(x_63, 0, x_1);
lean_closure_set(x_63, 1, x_61);
lean_closure_set(x_63, 2, x_2);
lean_closure_set(x_63, 3, x_3);
lean_closure_set(x_63, 4, x_4);
lean_closure_set(x_63, 5, x_5);
lean_closure_set(x_63, 6, x_6);
lean_closure_set(x_63, 7, x_7);
lean_closure_set(x_63, 8, x_62);
if (x_60 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_16);
lean_ctor_set(x_66, 1, x_56);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_apply_2(x_65, lean_box(0), x_67);
x_69 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_68, x_63);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_70 = x_16;
} else {
 lean_dec_ref(x_16);
 x_70 = lean_box(0);
}
x_71 = lean_array_fget(x_57, x_58);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_58, x_72);
lean_dec(x_58);
if (lean_is_scalar(x_70)) {
 x_74 = lean_alloc_ctor(0, 3, 0);
} else {
 x_74 = x_70;
}
lean_ctor_set(x_74, 0, x_57);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_59);
x_75 = l_Lean_Syntax_getId(x_15);
x_76 = lean_box(0);
lean_inc(x_15);
lean_inc(x_1);
x_77 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___rarg(x_1, x_5, x_3, x_2, x_4, x_15, x_75, x_76);
lean_inc(x_6);
x_78 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__3), 7, 6);
lean_closure_set(x_78, 0, x_15);
lean_closure_set(x_78, 1, x_71);
lean_closure_set(x_78, 2, x_56);
lean_closure_set(x_78, 3, x_1);
lean_closure_set(x_78, 4, x_74);
lean_closure_set(x_78, 5, x_6);
x_79 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_77, x_78);
x_80 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_79, x_63);
return x_80;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getOptDerivingClasses___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_getOptDerivingClasses___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Elab_getOptDerivingClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getOptDerivingClasses___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_getOptDerivingClasses___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Elab_DerivingClassView_applyHandlers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_elabDeriving___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Deriving");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__1;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__3;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Deriving_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
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
l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__3 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_elabDeriving___spec__10___closed__3);
l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1 = _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__1);
l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2 = _init_l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_elabDeriving___spec__7___closed__2);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__1 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__1();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__1);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__2 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__2();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__2);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__3 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__3();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_elabDeriving___spec__15___closed__3);
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
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232____closed__3);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Deriving_Basic___hyg_1232_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
