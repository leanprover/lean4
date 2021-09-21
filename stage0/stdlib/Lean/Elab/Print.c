// Lean compiler output
// Module: Lean.Elab.Print
// Imports: Init Lean.Util.FoldConsts Lean.Elab.Command
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7;
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_String_instInhabitedString;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4;
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__1;
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__3;
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__17;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__4;
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__3;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__5;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
extern lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__12;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__2;
extern lean_object* l_Lean_protectedExt;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__11;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_CollectAxioms_State_axioms___default;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
static lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__2;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_CollectAxioms_State_visited___default;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__10;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__16;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_CollectAxioms_State_axioms___default___closed__1;
static lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_CollectAxioms_collect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6;
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__15;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__3;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__5;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__18;
static lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__6;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__14;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown identifier '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = l_Lean_mkConst(x_1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3;
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_1 = x_4;
x_2 = x_8;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".{");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("}");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1(x_4, x_9);
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("protected ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unsafe ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("partial ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
switch (x_5) {
case 0:
{
lean_object* x_148; 
x_148 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15;
x_10 = x_148;
goto block_147;
}
case 1:
{
lean_object* x_149; 
x_149 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
x_10 = x_149;
goto block_147;
}
default: 
{
lean_object* x_150; 
x_150 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18;
x_10 = x_150;
goto block_147;
}
}
block_147:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_protectedExt;
lean_inc(x_2);
x_15 = l_Lean_TagDeclarationExtension_isTagged(x_14, x_13, x_2);
lean_inc(x_2);
x_16 = lean_private_to_user_name(x_2);
if (x_15 == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_4);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
lean_dec(x_16);
x_31 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_30);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_4);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_9, 0, x_45);
return x_9;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_46);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_2);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_4);
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_9, 0, x_60);
return x_9;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_2);
x_61 = lean_ctor_get(x_16, 0);
lean_inc(x_61);
lean_dec(x_16);
x_62 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_47);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_1);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_69, 0, x_61);
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_4);
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_9, 0, x_76);
return x_9;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_9, 0);
x_78 = lean_ctor_get(x_9, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_9);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_protectedExt;
lean_inc(x_2);
x_81 = l_Lean_TagDeclarationExtension_isTagged(x_80, x_79, x_2);
lean_inc(x_2);
x_82 = lean_private_to_user_name(x_2);
if (x_81 == 0)
{
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_1);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_10);
lean_ctor_set(x_85, 1, x_84);
x_86 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_88, 0, x_2);
x_89 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_4);
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_78);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_2);
x_97 = lean_ctor_get(x_82, 0);
lean_inc(x_97);
lean_dec(x_82);
x_98 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_10);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_100, 0, x_1);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_105, 0, x_97);
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_111, 0, x_4);
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_78);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12;
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_10);
lean_ctor_set(x_115, 1, x_114);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_1);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_121, 0, x_2);
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_4);
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_78);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_2);
x_130 = lean_ctor_get(x_82, 0);
lean_inc(x_130);
lean_dec(x_82);
x_131 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
x_132 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_132, 0, x_115);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_1);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
x_136 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_137 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_138, 0, x_130);
x_139 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_4);
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_78);
return x_146;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_5 == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" :=");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_5);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = 0;
x_20 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_18, x_19, x_7, x_8, x_12);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_10, x_12, x_6, x_7, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Quotient primitive");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1;
x_8 = 0;
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_7, x_1, x_2, x_3, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown constant '");
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2(x_17, x_2, x_3, x_8);
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
x_27 = l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2(x_30, x_2, x_3, x_21);
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_8);
x_10 = l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(x_8, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_ConstantInfo_type(x_11);
lean_dec(x_11);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_2 = x_9;
x_3 = x_20;
x_6 = x_12;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructors:");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1;
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(x_11, x_1, x_2, x_5, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_8);
x_19 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__3(x_15, x_6, x_18, x_8, x_9, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
x_23 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_20, x_22, x_8, x_9, x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("axiom");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("def");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("theorem");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructor");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursor");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_9 = lean_environment_find(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(x_1, x_2, x_3, x_7);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1;
x_18 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_17, x_1, x_15, x_16, x_14, x_2, x_3, x_7);
lean_dec(x_15);
return x_18;
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2;
x_26 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_25, x_1, x_23, x_24, x_21, x_22, x_2, x_3, x_7);
lean_dec(x_23);
return x_26;
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3;
x_33 = 1;
x_34 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_32, x_1, x_30, x_31, x_29, x_33, x_2, x_3, x_7);
lean_dec(x_30);
return x_34;
}
case 3:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 2);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4;
x_41 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_40, x_1, x_38, x_39, x_37, x_2, x_3, x_7);
lean_dec(x_38);
return x_41;
}
case 4:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
lean_dec(x_11);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 2);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1;
x_47 = 0;
x_48 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_46, x_1, x_44, x_45, x_47, x_2, x_3, x_7);
lean_dec(x_44);
return x_48;
}
case 5:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
lean_dec(x_11);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 4);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_49, sizeof(void*)*5 + 1);
lean_dec(x_49);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 2);
lean_inc(x_56);
lean_dec(x_50);
x_57 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(x_1, x_55, x_51, x_52, x_56, x_53, x_54, x_2, x_3, x_7);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_55);
return x_57;
}
case 6:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_11, 0);
lean_inc(x_58);
lean_dec(x_11);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_58, sizeof(void*)*5);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 2);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5;
x_64 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_63, x_1, x_61, x_62, x_60, x_2, x_3, x_7);
lean_dec(x_61);
return x_64;
}
default: 
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_11, 0);
lean_inc(x_65);
lean_dec(x_11);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_65, sizeof(void*)*7 + 1);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 2);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6;
x_71 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_70, x_1, x_68, x_69, x_67, x_2, x_3, x_7);
lean_dec(x_68);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = l_Lean_mkConst(x_1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5(x_1, x_2, x_3, x_4);
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
x_12 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___lambda__1(x_9, x_8, x_11, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_9);
x_13 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6(x_1, x_2, x_3, x_7);
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
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected identifier");
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_16 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(x_5, x_2, x_3, x_12);
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
x_24 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(x_5, x_23, x_3, x_12);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__3;
x_26 = l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3(x_1, x_25, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__2;
x_3 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_16 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9(x_17, x_2, x_3, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_5);
x_11 = l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = l_Lean_LocalContext_empty;
x_17 = 0;
lean_inc(x_2);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 3, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8(x_19, x_5, x_6, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_3 = x_10;
x_4 = x_22;
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(x_1, x_3, x_4, x_5);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_box(0);
lean_inc(x_7);
x_19 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__10(x_1, x_2, x_7, x_18, x_3, x_4, x_17);
lean_dec(x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_6);
if (x_28 == 0)
{
return x_6;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_1 = x_8;
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_List_forM___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__11(x_7, x_2, x_3, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabPrint___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__2;
x_2 = l_Lean_Elab_Command_elabPrint___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__4;
x_2 = l_Lean_Elab_Command_elabPrint___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("print");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__6;
x_2 = l_Lean_Elab_Command_elabPrint___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid #print command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabPrint___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("strLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabPrint___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.Option.BasicAux");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option.get!");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("value is none");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__15;
x_2 = l_Lean_Elab_Command_elabPrint___closed__16;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Elab_Command_elabPrint___closed__17;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabPrint___closed__8;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_Elab_Command_elabPrint___closed__10;
x_8 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_7, x_2, x_3, x_4);
lean_dec(x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_Lean_Elab_Command_elabPrint___closed__12;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Command_elabPrint___closed__14;
lean_inc(x_12);
x_16 = l_Lean_Syntax_isOfKind(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_10);
x_17 = l_Lean_Elab_Command_elabPrint___closed__10;
x_18 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_17, x_2, x_3, x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Syntax_isStrLit_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_20 = l_String_instInhabitedString;
x_21 = l_Lean_Elab_Command_elabPrint___closed__18;
x_22 = lean_panic_fn(x_20, x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = 0;
x_26 = l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_10, x_24, x_25, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_10);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = 0;
x_31 = l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_10, x_29, x_30, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_10);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_replaceRef(x_10, x_33);
lean_dec(x_33);
lean_dec(x_10);
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_2, 6);
lean_dec(x_37);
lean_ctor_set(x_2, 6, x_35);
x_38 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(x_12, x_2, x_3, x_34);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
x_42 = lean_ctor_get(x_2, 3);
x_43 = lean_ctor_get(x_2, 4);
x_44 = lean_ctor_get(x_2, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_45 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
lean_ctor_set(x_45, 5, x_44);
lean_ctor_set(x_45, 6, x_35);
x_46 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(x_12, x_45, x_3, x_34);
return x_46;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2;
x_2 = l_Lean_Elab_Command_elabPrint___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabPrint");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrint), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Elab_Command_elabPrint___closed__8;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__5;
x_5 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_CollectAxioms_State_visited___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_CollectAxioms_State_axioms___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_CollectAxioms_State_axioms___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CollectAxioms_State_axioms___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_2 == x_3;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lean_Elab_Command_CollectAxioms_collect(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = x_2 + x_12;
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = l_Lean_Elab_Command_CollectAxioms_collect(x_6, x_2, x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_CollectAxioms_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Lean_NameSet_contains(x_4, x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_inc(x_1);
x_11 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_1, x_10);
lean_inc(x_5);
lean_inc(x_11);
lean_ctor_set(x_3, 0, x_11);
lean_inc(x_1);
lean_inc(x_2);
x_12 = lean_environment_find(x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_array_push(x_5, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Expr_getUsedConstants(x_20);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_49; 
lean_dec(x_22);
lean_dec(x_21);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_10);
lean_ctor_set(x_49, 1, x_3);
x_25 = x_49;
goto block_48;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_22, x_22);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_22);
lean_dec(x_21);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_10);
lean_ctor_set(x_51, 1, x_3);
x_25 = x_51;
goto block_48;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_22);
lean_dec(x_22);
lean_inc(x_2);
x_54 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_21, x_52, x_53, x_10, x_2, x_3);
lean_dec(x_21);
x_25 = x_54;
goto block_48;
}
}
block_48:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = l_Lean_Expr_getUsedConstants(x_29);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_23, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_10);
return x_25;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_2);
lean_ctor_set(x_25, 0, x_10);
return x_25;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
lean_free_object(x_25);
x_34 = 0;
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_30, x_34, x_35, x_10, x_2, x_27);
lean_dec(x_30);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_dec(x_18);
x_39 = l_Lean_Expr_getUsedConstants(x_38);
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_lt(x_23, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_40, x_40);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_10);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_47 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_39, x_45, x_46, x_10, x_2, x_37);
lean_dec(x_39);
return x_47;
}
}
}
}
}
case 2:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_55 = lean_ctor_get(x_14, 0);
lean_inc(x_55);
lean_dec(x_14);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 2);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Expr_getUsedConstants(x_57);
x_59 = lean_array_get_size(x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
if (x_61 == 0)
{
lean_object* x_86; 
lean_dec(x_59);
lean_dec(x_58);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_10);
lean_ctor_set(x_86, 1, x_3);
x_62 = x_86;
goto block_85;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_59, x_59);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_59);
lean_dec(x_58);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_10);
lean_ctor_set(x_88, 1, x_3);
x_62 = x_88;
goto block_85;
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_59);
lean_dec(x_59);
lean_inc(x_2);
x_91 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_58, x_89, x_90, x_10, x_2, x_3);
lean_dec(x_58);
x_62 = x_91;
goto block_85;
}
}
block_85:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_62, 1);
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
lean_dec(x_55);
x_67 = l_Lean_Expr_getUsedConstants(x_66);
x_68 = lean_array_get_size(x_67);
x_69 = lean_nat_dec_lt(x_60, x_68);
if (x_69 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_2);
lean_ctor_set(x_62, 0, x_10);
return x_62;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_68, x_68);
if (x_70 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_2);
lean_ctor_set(x_62, 0, x_10);
return x_62;
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; 
lean_free_object(x_62);
x_71 = 0;
x_72 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_73 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_67, x_71, x_72, x_10, x_2, x_64);
lean_dec(x_67);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
lean_dec(x_62);
x_75 = lean_ctor_get(x_55, 1);
lean_inc(x_75);
lean_dec(x_55);
x_76 = l_Lean_Expr_getUsedConstants(x_75);
x_77 = lean_array_get_size(x_76);
x_78 = lean_nat_dec_lt(x_60, x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_2);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_10);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_77, x_77);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_10);
lean_ctor_set(x_81, 1, x_74);
return x_81;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_84 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_76, x_82, x_83, x_10, x_2, x_74);
lean_dec(x_76);
return x_84;
}
}
}
}
}
case 3:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_92 = lean_ctor_get(x_14, 0);
lean_inc(x_92);
lean_dec(x_14);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 2);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Lean_Expr_getUsedConstants(x_94);
x_96 = lean_array_get_size(x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_lt(x_97, x_96);
if (x_98 == 0)
{
lean_object* x_123; 
lean_dec(x_96);
lean_dec(x_95);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_10);
lean_ctor_set(x_123, 1, x_3);
x_99 = x_123;
goto block_122;
}
else
{
uint8_t x_124; 
x_124 = lean_nat_dec_le(x_96, x_96);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_96);
lean_dec(x_95);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_10);
lean_ctor_set(x_125, 1, x_3);
x_99 = x_125;
goto block_122;
}
else
{
size_t x_126; size_t x_127; lean_object* x_128; 
x_126 = 0;
x_127 = lean_usize_of_nat(x_96);
lean_dec(x_96);
lean_inc(x_2);
x_128 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_95, x_126, x_127, x_10, x_2, x_3);
lean_dec(x_95);
x_99 = x_128;
goto block_122;
}
}
block_122:
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_99, 1);
x_102 = lean_ctor_get(x_99, 0);
lean_dec(x_102);
x_103 = lean_ctor_get(x_92, 1);
lean_inc(x_103);
lean_dec(x_92);
x_104 = l_Lean_Expr_getUsedConstants(x_103);
x_105 = lean_array_get_size(x_104);
x_106 = lean_nat_dec_lt(x_97, x_105);
if (x_106 == 0)
{
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_2);
lean_ctor_set(x_99, 0, x_10);
return x_99;
}
else
{
uint8_t x_107; 
x_107 = lean_nat_dec_le(x_105, x_105);
if (x_107 == 0)
{
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_2);
lean_ctor_set(x_99, 0, x_10);
return x_99;
}
else
{
size_t x_108; size_t x_109; lean_object* x_110; 
lean_free_object(x_99);
x_108 = 0;
x_109 = lean_usize_of_nat(x_105);
lean_dec(x_105);
x_110 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_104, x_108, x_109, x_10, x_2, x_101);
lean_dec(x_104);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
lean_dec(x_99);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
lean_dec(x_92);
x_113 = l_Lean_Expr_getUsedConstants(x_112);
x_114 = lean_array_get_size(x_113);
x_115 = lean_nat_dec_lt(x_97, x_114);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_2);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_10);
lean_ctor_set(x_116, 1, x_111);
return x_116;
}
else
{
uint8_t x_117; 
x_117 = lean_nat_dec_le(x_114, x_114);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_2);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_10);
lean_ctor_set(x_118, 1, x_111);
return x_118;
}
else
{
size_t x_119; size_t x_120; lean_object* x_121; 
x_119 = 0;
x_120 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_121 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_113, x_119, x_120, x_10, x_2, x_111);
lean_dec(x_113);
return x_121;
}
}
}
}
}
case 4:
{
lean_object* x_129; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_10);
lean_ctor_set(x_129, 1, x_3);
return x_129;
}
case 5:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_130 = lean_ctor_get(x_14, 0);
lean_inc(x_130);
lean_dec(x_14);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 2);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Expr_getUsedConstants(x_132);
x_134 = lean_array_get_size(x_133);
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_nat_dec_lt(x_135, x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_134);
lean_dec(x_133);
x_137 = lean_ctor_get(x_130, 4);
lean_inc(x_137);
lean_dec(x_130);
x_138 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_137, x_2, x_3);
return x_138;
}
else
{
uint8_t x_139; 
x_139 = lean_nat_dec_le(x_134, x_134);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_134);
lean_dec(x_133);
x_140 = lean_ctor_get(x_130, 4);
lean_inc(x_140);
lean_dec(x_130);
x_141 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_140, x_2, x_3);
return x_141;
}
else
{
size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = 0;
x_143 = lean_usize_of_nat(x_134);
lean_dec(x_134);
lean_inc(x_2);
x_144 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_133, x_142, x_143, x_10, x_2, x_3);
lean_dec(x_133);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_ctor_get(x_130, 4);
lean_inc(x_146);
lean_dec(x_130);
x_147 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_146, x_2, x_145);
return x_147;
}
}
}
default: 
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_148 = lean_ctor_get(x_14, 0);
lean_inc(x_148);
lean_dec(x_14);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_ctor_get(x_149, 2);
lean_inc(x_150);
lean_dec(x_149);
x_151 = l_Lean_Expr_getUsedConstants(x_150);
x_152 = lean_array_get_size(x_151);
x_153 = lean_unsigned_to_nat(0u);
x_154 = lean_nat_dec_lt(x_153, x_152);
if (x_154 == 0)
{
lean_object* x_155; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_2);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_10);
lean_ctor_set(x_155, 1, x_3);
return x_155;
}
else
{
uint8_t x_156; 
x_156 = lean_nat_dec_le(x_152, x_152);
if (x_156 == 0)
{
lean_object* x_157; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_2);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_10);
lean_ctor_set(x_157, 1, x_3);
return x_157;
}
else
{
size_t x_158; size_t x_159; lean_object* x_160; 
x_158 = 0;
x_159 = lean_usize_of_nat(x_152);
lean_dec(x_152);
x_160 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_151, x_158, x_159, x_10, x_2, x_3);
lean_dec(x_151);
return x_160;
}
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_3);
x_161 = lean_box(0);
lean_inc(x_1);
x_162 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_1, x_161);
lean_inc(x_5);
lean_inc(x_162);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_5);
lean_inc(x_1);
lean_inc(x_2);
x_164 = lean_environment_find(x_2, x_1);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_dec(x_162);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
else
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
switch (lean_obj_tag(x_166)) {
case 0:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_166);
lean_dec(x_163);
lean_dec(x_2);
x_167 = lean_array_push(x_5, x_1);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_161);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
case 1:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
lean_dec(x_162);
lean_dec(x_5);
lean_dec(x_1);
x_170 = lean_ctor_get(x_166, 0);
lean_inc(x_170);
lean_dec(x_166);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 2);
lean_inc(x_172);
lean_dec(x_171);
x_173 = l_Lean_Expr_getUsedConstants(x_172);
x_174 = lean_array_get_size(x_173);
x_175 = lean_unsigned_to_nat(0u);
x_176 = lean_nat_dec_lt(x_175, x_174);
if (x_176 == 0)
{
lean_object* x_191; 
lean_dec(x_174);
lean_dec(x_173);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_161);
lean_ctor_set(x_191, 1, x_163);
x_177 = x_191;
goto block_190;
}
else
{
uint8_t x_192; 
x_192 = lean_nat_dec_le(x_174, x_174);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_174);
lean_dec(x_173);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_161);
lean_ctor_set(x_193, 1, x_163);
x_177 = x_193;
goto block_190;
}
else
{
size_t x_194; size_t x_195; lean_object* x_196; 
x_194 = 0;
x_195 = lean_usize_of_nat(x_174);
lean_dec(x_174);
lean_inc(x_2);
x_196 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_173, x_194, x_195, x_161, x_2, x_163);
lean_dec(x_173);
x_177 = x_196;
goto block_190;
}
}
block_190:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
lean_dec(x_170);
x_181 = l_Lean_Expr_getUsedConstants(x_180);
x_182 = lean_array_get_size(x_181);
x_183 = lean_nat_dec_lt(x_175, x_182);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_2);
if (lean_is_scalar(x_179)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_179;
}
lean_ctor_set(x_184, 0, x_161);
lean_ctor_set(x_184, 1, x_178);
return x_184;
}
else
{
uint8_t x_185; 
x_185 = lean_nat_dec_le(x_182, x_182);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_2);
if (lean_is_scalar(x_179)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_179;
}
lean_ctor_set(x_186, 0, x_161);
lean_ctor_set(x_186, 1, x_178);
return x_186;
}
else
{
size_t x_187; size_t x_188; lean_object* x_189; 
lean_dec(x_179);
x_187 = 0;
x_188 = lean_usize_of_nat(x_182);
lean_dec(x_182);
x_189 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_181, x_187, x_188, x_161, x_2, x_178);
lean_dec(x_181);
return x_189;
}
}
}
}
case 2:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; 
lean_dec(x_162);
lean_dec(x_5);
lean_dec(x_1);
x_197 = lean_ctor_get(x_166, 0);
lean_inc(x_197);
lean_dec(x_166);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_198, 2);
lean_inc(x_199);
lean_dec(x_198);
x_200 = l_Lean_Expr_getUsedConstants(x_199);
x_201 = lean_array_get_size(x_200);
x_202 = lean_unsigned_to_nat(0u);
x_203 = lean_nat_dec_lt(x_202, x_201);
if (x_203 == 0)
{
lean_object* x_218; 
lean_dec(x_201);
lean_dec(x_200);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_161);
lean_ctor_set(x_218, 1, x_163);
x_204 = x_218;
goto block_217;
}
else
{
uint8_t x_219; 
x_219 = lean_nat_dec_le(x_201, x_201);
if (x_219 == 0)
{
lean_object* x_220; 
lean_dec(x_201);
lean_dec(x_200);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_161);
lean_ctor_set(x_220, 1, x_163);
x_204 = x_220;
goto block_217;
}
else
{
size_t x_221; size_t x_222; lean_object* x_223; 
x_221 = 0;
x_222 = lean_usize_of_nat(x_201);
lean_dec(x_201);
lean_inc(x_2);
x_223 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_200, x_221, x_222, x_161, x_2, x_163);
lean_dec(x_200);
x_204 = x_223;
goto block_217;
}
}
block_217:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_197, 1);
lean_inc(x_207);
lean_dec(x_197);
x_208 = l_Lean_Expr_getUsedConstants(x_207);
x_209 = lean_array_get_size(x_208);
x_210 = lean_nat_dec_lt(x_202, x_209);
if (x_210 == 0)
{
lean_object* x_211; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_2);
if (lean_is_scalar(x_206)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_206;
}
lean_ctor_set(x_211, 0, x_161);
lean_ctor_set(x_211, 1, x_205);
return x_211;
}
else
{
uint8_t x_212; 
x_212 = lean_nat_dec_le(x_209, x_209);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_2);
if (lean_is_scalar(x_206)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_206;
}
lean_ctor_set(x_213, 0, x_161);
lean_ctor_set(x_213, 1, x_205);
return x_213;
}
else
{
size_t x_214; size_t x_215; lean_object* x_216; 
lean_dec(x_206);
x_214 = 0;
x_215 = lean_usize_of_nat(x_209);
lean_dec(x_209);
x_216 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_208, x_214, x_215, x_161, x_2, x_205);
lean_dec(x_208);
return x_216;
}
}
}
}
case 3:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; 
lean_dec(x_162);
lean_dec(x_5);
lean_dec(x_1);
x_224 = lean_ctor_get(x_166, 0);
lean_inc(x_224);
lean_dec(x_166);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 2);
lean_inc(x_226);
lean_dec(x_225);
x_227 = l_Lean_Expr_getUsedConstants(x_226);
x_228 = lean_array_get_size(x_227);
x_229 = lean_unsigned_to_nat(0u);
x_230 = lean_nat_dec_lt(x_229, x_228);
if (x_230 == 0)
{
lean_object* x_245; 
lean_dec(x_228);
lean_dec(x_227);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_161);
lean_ctor_set(x_245, 1, x_163);
x_231 = x_245;
goto block_244;
}
else
{
uint8_t x_246; 
x_246 = lean_nat_dec_le(x_228, x_228);
if (x_246 == 0)
{
lean_object* x_247; 
lean_dec(x_228);
lean_dec(x_227);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_161);
lean_ctor_set(x_247, 1, x_163);
x_231 = x_247;
goto block_244;
}
else
{
size_t x_248; size_t x_249; lean_object* x_250; 
x_248 = 0;
x_249 = lean_usize_of_nat(x_228);
lean_dec(x_228);
lean_inc(x_2);
x_250 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_227, x_248, x_249, x_161, x_2, x_163);
lean_dec(x_227);
x_231 = x_250;
goto block_244;
}
}
block_244:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_224, 1);
lean_inc(x_234);
lean_dec(x_224);
x_235 = l_Lean_Expr_getUsedConstants(x_234);
x_236 = lean_array_get_size(x_235);
x_237 = lean_nat_dec_lt(x_229, x_236);
if (x_237 == 0)
{
lean_object* x_238; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_2);
if (lean_is_scalar(x_233)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_233;
}
lean_ctor_set(x_238, 0, x_161);
lean_ctor_set(x_238, 1, x_232);
return x_238;
}
else
{
uint8_t x_239; 
x_239 = lean_nat_dec_le(x_236, x_236);
if (x_239 == 0)
{
lean_object* x_240; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_2);
if (lean_is_scalar(x_233)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_233;
}
lean_ctor_set(x_240, 0, x_161);
lean_ctor_set(x_240, 1, x_232);
return x_240;
}
else
{
size_t x_241; size_t x_242; lean_object* x_243; 
lean_dec(x_233);
x_241 = 0;
x_242 = lean_usize_of_nat(x_236);
lean_dec(x_236);
x_243 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_235, x_241, x_242, x_161, x_2, x_232);
lean_dec(x_235);
return x_243;
}
}
}
}
case 4:
{
lean_object* x_251; 
lean_dec(x_166);
lean_dec(x_162);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_161);
lean_ctor_set(x_251, 1, x_163);
return x_251;
}
case 5:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_dec(x_162);
lean_dec(x_5);
lean_dec(x_1);
x_252 = lean_ctor_get(x_166, 0);
lean_inc(x_252);
lean_dec(x_166);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_253, 2);
lean_inc(x_254);
lean_dec(x_253);
x_255 = l_Lean_Expr_getUsedConstants(x_254);
x_256 = lean_array_get_size(x_255);
x_257 = lean_unsigned_to_nat(0u);
x_258 = lean_nat_dec_lt(x_257, x_256);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_256);
lean_dec(x_255);
x_259 = lean_ctor_get(x_252, 4);
lean_inc(x_259);
lean_dec(x_252);
x_260 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_259, x_2, x_163);
return x_260;
}
else
{
uint8_t x_261; 
x_261 = lean_nat_dec_le(x_256, x_256);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_256);
lean_dec(x_255);
x_262 = lean_ctor_get(x_252, 4);
lean_inc(x_262);
lean_dec(x_252);
x_263 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_262, x_2, x_163);
return x_263;
}
else
{
size_t x_264; size_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_264 = 0;
x_265 = lean_usize_of_nat(x_256);
lean_dec(x_256);
lean_inc(x_2);
x_266 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_255, x_264, x_265, x_161, x_2, x_163);
lean_dec(x_255);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = lean_ctor_get(x_252, 4);
lean_inc(x_268);
lean_dec(x_252);
x_269 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_268, x_2, x_267);
return x_269;
}
}
}
default: 
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
lean_dec(x_162);
lean_dec(x_5);
lean_dec(x_1);
x_270 = lean_ctor_get(x_166, 0);
lean_inc(x_270);
lean_dec(x_166);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec(x_270);
x_272 = lean_ctor_get(x_271, 2);
lean_inc(x_272);
lean_dec(x_271);
x_273 = l_Lean_Expr_getUsedConstants(x_272);
x_274 = lean_array_get_size(x_273);
x_275 = lean_unsigned_to_nat(0u);
x_276 = lean_nat_dec_lt(x_275, x_274);
if (x_276 == 0)
{
lean_object* x_277; 
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_2);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_161);
lean_ctor_set(x_277, 1, x_163);
return x_277;
}
else
{
uint8_t x_278; 
x_278 = lean_nat_dec_le(x_274, x_274);
if (x_278 == 0)
{
lean_object* x_279; 
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_2);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_161);
lean_ctor_set(x_279, 1, x_163);
return x_279;
}
else
{
size_t x_280; size_t x_281; lean_object* x_282; 
x_280 = 0;
x_281 = lean_usize_of_nat(x_274);
lean_dec(x_274);
x_282 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_273, x_280, x_281, x_161, x_2, x_163);
lean_dec(x_273);
return x_282;
}
}
}
}
}
}
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_283 = lean_box(0);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_3);
return x_284;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_Elab_Command_CollectAxioms_State_axioms___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' depends on axioms: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not depend on any axioms");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1;
lean_inc(x_1);
x_10 = l_Lean_Elab_Command_CollectAxioms_collect(x_1, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Array_isEmpty___rarg(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_to_list(lean_box(0), x_12);
x_20 = lean_box(0);
x_21 = l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(x_19, x_20);
x_22 = l_Lean_MessageData_ofList(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = 0;
x_27 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_25, x_26, x_2, x_3, x_7);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_12);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_1);
x_29 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = 0;
x_34 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_32, x_33, x_2, x_3, x_7);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(x_7, x_2, x_3, x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_1 = x_8;
x_4 = x_10;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrintAxioms___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("printAxioms");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrintAxioms___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__6;
x_2 = l_Lean_Elab_Command_elabPrintAxioms___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabPrintAxioms___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_replaceRef(x_9, x_14);
lean_dec(x_14);
lean_dec(x_9);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 6);
lean_dec(x_18);
lean_ctor_set(x_2, 6, x_16);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(x_11, x_12, x_2, x_3, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(x_20, x_2, x_3, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_3);
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
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get(x_2, 3);
x_31 = lean_ctor_get(x_2, 4);
x_32 = lean_ctor_get(x_2, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_16);
lean_inc(x_3);
lean_inc(x_33);
x_34 = l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(x_11, x_12, x_33, x_3, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(x_35, x_33, x_3, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
lean_dec(x_3);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_40 = x_34;
} else {
 lean_dec_ref(x_34);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabPrintAxioms");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrintAxioms), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Elab_Command_elabPrintAxioms___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Print(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4);
l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2);
l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3 = _init_l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1);
l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__1 = _init_l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__1);
l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__2 = _init_l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__1 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__1);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__2 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__2);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__3 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___closed__3);
l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__1 = _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__1();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__1);
l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__2 = _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__2();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__2);
l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__3 = _init_l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__3();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___closed__3);
l_Lean_Elab_Command_elabPrint___closed__1 = _init_l_Lean_Elab_Command_elabPrint___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__1);
l_Lean_Elab_Command_elabPrint___closed__2 = _init_l_Lean_Elab_Command_elabPrint___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__2);
l_Lean_Elab_Command_elabPrint___closed__3 = _init_l_Lean_Elab_Command_elabPrint___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__3);
l_Lean_Elab_Command_elabPrint___closed__4 = _init_l_Lean_Elab_Command_elabPrint___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__4);
l_Lean_Elab_Command_elabPrint___closed__5 = _init_l_Lean_Elab_Command_elabPrint___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__5);
l_Lean_Elab_Command_elabPrint___closed__6 = _init_l_Lean_Elab_Command_elabPrint___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__6);
l_Lean_Elab_Command_elabPrint___closed__7 = _init_l_Lean_Elab_Command_elabPrint___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__7);
l_Lean_Elab_Command_elabPrint___closed__8 = _init_l_Lean_Elab_Command_elabPrint___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__8);
l_Lean_Elab_Command_elabPrint___closed__9 = _init_l_Lean_Elab_Command_elabPrint___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__9);
l_Lean_Elab_Command_elabPrint___closed__10 = _init_l_Lean_Elab_Command_elabPrint___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__10);
l_Lean_Elab_Command_elabPrint___closed__11 = _init_l_Lean_Elab_Command_elabPrint___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__11);
l_Lean_Elab_Command_elabPrint___closed__12 = _init_l_Lean_Elab_Command_elabPrint___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__12);
l_Lean_Elab_Command_elabPrint___closed__13 = _init_l_Lean_Elab_Command_elabPrint___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__13);
l_Lean_Elab_Command_elabPrint___closed__14 = _init_l_Lean_Elab_Command_elabPrint___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__14);
l_Lean_Elab_Command_elabPrint___closed__15 = _init_l_Lean_Elab_Command_elabPrint___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__15);
l_Lean_Elab_Command_elabPrint___closed__16 = _init_l_Lean_Elab_Command_elabPrint___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__16);
l_Lean_Elab_Command_elabPrint___closed__17 = _init_l_Lean_Elab_Command_elabPrint___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__17);
l_Lean_Elab_Command_elabPrint___closed__18 = _init_l_Lean_Elab_Command_elabPrint___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__18);
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3);
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4);
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__5);
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__6);
res = l___regBuiltin_Lean_Elab_Command_elabPrint(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_CollectAxioms_State_visited___default = _init_l_Lean_Elab_Command_CollectAxioms_State_visited___default();
lean_mark_persistent(l_Lean_Elab_Command_CollectAxioms_State_visited___default);
l_Lean_Elab_Command_CollectAxioms_State_axioms___default___closed__1 = _init_l_Lean_Elab_Command_CollectAxioms_State_axioms___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CollectAxioms_State_axioms___default___closed__1);
l_Lean_Elab_Command_CollectAxioms_State_axioms___default = _init_l_Lean_Elab_Command_CollectAxioms_State_axioms___default();
lean_mark_persistent(l_Lean_Elab_Command_CollectAxioms_State_axioms___default);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1);
l_Lean_Elab_Command_elabPrintAxioms___closed__1 = _init_l_Lean_Elab_Command_elabPrintAxioms___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabPrintAxioms___closed__1);
l_Lean_Elab_Command_elabPrintAxioms___closed__2 = _init_l_Lean_Elab_Command_elabPrintAxioms___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabPrintAxioms___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
