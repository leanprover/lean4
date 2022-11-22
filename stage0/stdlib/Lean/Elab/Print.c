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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__4;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__6;
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_expandDeclId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__6;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint(lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Command_expandDeclId___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__4;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__5;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__5;
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__2;
lean_object* l_List_filterTR_loop___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
extern lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(lean_object*, lean_object*);
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_resolveGlobalConstCore___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
extern lean_object* l_Lean_protectedExt;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__11;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Command_expandDeclId___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_CollectAxioms_State_axioms___default;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
static lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_CollectAxioms_State_visited___default;
static lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__10;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__6;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5;
static lean_object* l_Lean_Elab_Command_CollectAxioms_State_axioms___default___closed__1;
static lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_CollectAxioms_collect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__6;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__1;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__2;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__5;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24;
static lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__7;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__7;
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__5;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown identifier '", 20);
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
x_1 = lean_mk_string_from_bytes("'", 1);
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
x_6 = l_Lean_Expr_const___override(x_1, x_5);
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
x_1 = lean_mk_string_from_bytes(", ", 2);
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
x_1 = lean_mk_string_from_bytes("", 0);
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
x_1 = lean_mk_string_from_bytes(".{", 2);
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
x_1 = lean_mk_string_from_bytes("}", 1);
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
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_get_reducibility_status(x_8, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_get_reducibility_status(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_protectedExt;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("private ", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("protected ", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unsafe ", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("partial ", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@[reducible] ", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@[irreducible] ", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_158; 
lean_inc(x_2);
x_9 = l_Lean_getReducibilityStatus___at___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___spec__1(x_2, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
x_158 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_158) {
case 0:
{
lean_object* x_159; 
x_159 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22;
x_13 = x_159;
goto block_157;
}
case 1:
{
lean_object* x_160; 
x_160 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
x_13 = x_160;
goto block_157;
}
default: 
{
lean_object* x_161; 
x_161 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25;
x_13 = x_161;
goto block_157;
}
}
block_157:
{
lean_object* x_14; 
switch (x_5) {
case 0:
{
lean_object* x_154; 
x_154 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16;
x_14 = x_154;
goto block_153;
}
case 1:
{
lean_object* x_155; 
x_155 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
x_14 = x_155;
goto block_153;
}
default: 
{
lean_object* x_156; 
x_156 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19;
x_14 = x_156;
goto block_153;
}
}
block_153:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
lean_inc(x_2);
x_20 = l_Lean_TagDeclarationExtension_isTagged(x_19, x_18, x_2);
lean_inc(x_2);
x_21 = lean_private_to_user_name(x_2);
if (x_20 == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_1);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_4);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_12, 0, x_34);
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
lean_dec(x_21);
x_36 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_1);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_35);
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_4);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_12, 0, x_50);
return x_12;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_51);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_1);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_58, 0, x_2);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_4);
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_12, 0, x_65);
return x_12;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
x_66 = lean_ctor_get(x_21, 0);
lean_inc(x_66);
lean_dec(x_21);
x_67 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_52);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_1);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_74, 0, x_66);
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_4);
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_12, 0, x_81);
return x_12;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_12, 0);
x_83 = lean_ctor_get(x_12, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_12);
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_13);
lean_ctor_set(x_84, 1, x_14);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
lean_inc(x_2);
x_87 = l_Lean_TagDeclarationExtension_isTagged(x_86, x_85, x_2);
lean_inc(x_2);
x_88 = lean_private_to_user_name(x_2);
if (x_87 == 0)
{
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_1);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_90);
x_92 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_94, 0, x_2);
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_100, 0, x_4);
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_83);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_103 = lean_ctor_get(x_88, 0);
lean_inc(x_103);
lean_dec(x_88);
x_104 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_84);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_1);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_111, 0, x_103);
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_4);
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_83);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13;
x_121 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_121, 0, x_84);
lean_ctor_set(x_121, 1, x_120);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_1);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_127, 0, x_2);
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_130 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_132 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_4);
x_134 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_83);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_2);
x_136 = lean_ctor_get(x_88, 0);
lean_inc(x_136);
lean_dec(x_88);
x_137 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_138 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_138, 0, x_121);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_139, 0, x_1);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
x_142 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_144, 0, x_136);
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_149 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_150, 0, x_4);
x_151 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_83);
return x_152;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getReducibilityStatus___at___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
x_1 = lean_mk_string_from_bytes(" :=", 3);
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
x_20 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_18, x_19, x_7, x_8, x_12);
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
x_13 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_10, x_12, x_6, x_7, x_11);
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
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Quotient primitive", 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__1;
x_8 = 0;
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_7, x_1, x_2, x_3, x_8, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = l_Lean_getConstInfo___at_Lean_Elab_Command_expandDeclId___spec__9(x_8, x_4, x_5, x_6);
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
x_16 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
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
x_1 = lean_mk_string_from_bytes("inductive", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("number of parameters: ", 22);
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
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("constructors:", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1;
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(x_10, x_1, x_2, x_4, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Nat_repr(x_3);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
x_23 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_7);
x_25 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(x_14, x_5, x_24, x_7, x_8, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_26, x_28, x_7, x_8, x_27);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("axiom", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("def", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("theorem", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("opaque", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("constructor", 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("recursor", 8);
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
x_22 = lean_ctor_get_uint8(x_19, sizeof(void*)*4);
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
x_37 = lean_ctor_get_uint8(x_35, sizeof(void*)*3);
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
x_46 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__1;
x_47 = 0;
x_48 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_46, x_1, x_44, x_45, x_47, x_2, x_3, x_7);
lean_dec(x_44);
return x_48;
}
case 5:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
lean_dec(x_11);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 4);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_49, sizeof(void*)*5 + 1);
lean_dec(x_49);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 2);
lean_inc(x_55);
lean_dec(x_50);
x_56 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(x_1, x_54, x_51, x_55, x_52, x_53, x_2, x_3, x_7);
lean_dec(x_54);
return x_56;
}
case 6:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_11, 0);
lean_inc(x_57);
lean_dec(x_11);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_57, sizeof(void*)*5);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5;
x_63 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_62, x_1, x_60, x_61, x_59, x_2, x_3, x_7);
lean_dec(x_60);
return x_63;
}
default: 
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_11, 0);
lean_inc(x_64);
lean_dec(x_11);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_64, sizeof(void*)*7 + 1);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 2);
lean_inc(x_68);
lean_dec(x_65);
x_69 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6;
x_70 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_69, x_1, x_67, x_68, x_66, x_2, x_3, x_7);
lean_dec(x_67);
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_expandDeclId___spec__11(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__16(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__16(x_2, x_20, x_4, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_mapTR_loop___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_List_filterTR_loop___at_Lean_resolveGlobalConstCore___spec__1(x_6, x_8);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5___lambda__1(x_9, x_8, x_11, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_9);
x_13 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7(x_1, x_2, x_3, x_7);
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
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected identifier", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_16 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5(x_5, x_2, x_3, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 5);
x_23 = lean_ctor_get(x_2, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_22);
lean_ctor_set(x_24, 6, x_13);
lean_ctor_set(x_24, 7, x_23);
x_25 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5(x_5, x_24, x_3, x_12);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__3;
x_27 = l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(x_1, x_26, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_Command_expandDeclId___spec__8(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_Lean_LocalContext_empty;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_expandDeclId___spec__11(x_15, x_4, x_5, x_9);
lean_dec(x_4);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_Elab_addConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8(x_1, x_9, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_3 = x_10;
x_4 = x_13;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3(x_1, x_3, x_4, x_5);
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
x_19 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9(x_1, x_2, x_7, x_18, x_3, x_4, x_17);
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
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__5;
x_3 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4;
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
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__3;
x_2 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = lean_box(0);
x_7 = 0;
x_8 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__7;
lean_inc(x_1);
x_9 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_7);
x_10 = l_Lean_Elab_addCompletionInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(x_9, x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(x_1, x_6, x_2, x_3, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_forM___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__10(x_13, x_2, x_3, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addCompletionInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5);
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
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("print", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = l_Lean_Elab_Command_elabPrint___closed__2;
x_3 = l_Lean_Elab_Command_elabPrint___closed__3;
x_4 = l_Lean_Elab_Command_elabPrint___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid #print command", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabPrint___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("str", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabPrint___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabPrint___closed__5;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_Elab_Command_elabPrint___closed__7;
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
x_13 = l_Lean_Elab_Command_elabPrint___closed__9;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Command_elabPrint___closed__11;
lean_inc(x_12);
x_16 = l_Lean_Syntax_isOfKind(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_10);
x_17 = l_Lean_Elab_Command_elabPrint___closed__7;
x_18 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_17, x_2, x_3, x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = l_Lean_TSyntax_getString(x_12);
lean_dec(x_12);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = 0;
x_23 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_10, x_21, x_22, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_10);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_replaceRef(x_10, x_25);
lean_dec(x_25);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_2, 6);
lean_dec(x_29);
lean_ctor_set(x_2, 6, x_27);
x_30 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(x_12, x_2, x_3, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
x_35 = lean_ctor_get(x_2, 4);
x_36 = lean_ctor_get(x_2, 5);
x_37 = lean_ctor_get(x_2, 7);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_33);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_36);
lean_ctor_set(x_38, 6, x_27);
lean_ctor_set(x_38, 7, x_37);
x_39 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(x_12, x_38, x_3, x_26);
return x_39;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabPrint", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1;
x_3 = l_Lean_Elab_Command_elabPrint___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__5() {
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
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4;
x_3 = l_Lean_Elab_Command_elabPrint___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(84u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(87u);
x_2 = lean_unsigned_to_nat(66u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__1;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__2;
x_4 = lean_unsigned_to_nat(66u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(84u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(84u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__4;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__5;
x_4 = lean_unsigned_to_nat(45u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
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
x_7 = lean_usize_dec_eq(x_2, x_3);
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
x_13 = lean_usize_add(x_2, x_12);
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
x_11 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_1, x_10);
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
lean_dec(x_22);
lean_dec(x_21);
x_25 = x_3;
goto block_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_22, x_22);
if (x_37 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
x_25 = x_3;
goto block_36;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_22);
lean_dec(x_22);
lean_inc(x_2);
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_21, x_38, x_39, x_10, x_2, x_3);
lean_dec(x_21);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_25 = x_41;
goto block_36;
}
}
block_36:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_Expr_getUsedConstants(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_23, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_28, x_28);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_27, x_33, x_34, x_10, x_2, x_25);
lean_dec(x_27);
return x_35;
}
}
}
}
case 2:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Expr_getUsedConstants(x_44);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_lt(x_47, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
x_49 = x_3;
goto block_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_46, x_46);
if (x_61 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
x_49 = x_3;
goto block_60;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_46);
lean_dec(x_46);
lean_inc(x_2);
x_64 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_45, x_62, x_63, x_10, x_2, x_3);
lean_dec(x_45);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_49 = x_65;
goto block_60;
}
}
block_60:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = l_Lean_Expr_getUsedConstants(x_50);
x_52 = lean_array_get_size(x_51);
x_53 = lean_nat_dec_lt(x_47, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_2);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_10);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_52, x_52);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_51, x_57, x_58, x_10, x_2, x_49);
lean_dec(x_51);
return x_59;
}
}
}
}
case 3:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_66 = lean_ctor_get(x_14, 0);
lean_inc(x_66);
lean_dec(x_14);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 2);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Expr_getUsedConstants(x_68);
x_70 = lean_array_get_size(x_69);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_lt(x_71, x_70);
if (x_72 == 0)
{
lean_dec(x_70);
lean_dec(x_69);
x_73 = x_3;
goto block_84;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_70, x_70);
if (x_85 == 0)
{
lean_dec(x_70);
lean_dec(x_69);
x_73 = x_3;
goto block_84;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; lean_object* x_89; 
x_86 = 0;
x_87 = lean_usize_of_nat(x_70);
lean_dec(x_70);
lean_inc(x_2);
x_88 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_69, x_86, x_87, x_10, x_2, x_3);
lean_dec(x_69);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_73 = x_89;
goto block_84;
}
}
block_84:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
lean_dec(x_66);
x_75 = l_Lean_Expr_getUsedConstants(x_74);
x_76 = lean_array_get_size(x_75);
x_77 = lean_nat_dec_lt(x_71, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_10);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_76, x_76);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_10);
lean_ctor_set(x_80, 1, x_73);
return x_80;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_83 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_75, x_81, x_82, x_10, x_2, x_73);
lean_dec(x_75);
return x_83;
}
}
}
}
case 4:
{
lean_object* x_90; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_10);
lean_ctor_set(x_90, 1, x_3);
return x_90;
}
case 5:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_91 = lean_ctor_get(x_14, 0);
lean_inc(x_91);
lean_dec(x_14);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 2);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Expr_getUsedConstants(x_93);
x_95 = lean_array_get_size(x_94);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_lt(x_96, x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_95);
lean_dec(x_94);
x_98 = lean_ctor_get(x_91, 4);
lean_inc(x_98);
lean_dec(x_91);
x_99 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_98, x_2, x_3);
return x_99;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_95, x_95);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_94);
x_101 = lean_ctor_get(x_91, 4);
lean_inc(x_101);
lean_dec(x_91);
x_102 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_101, x_2, x_3);
return x_102;
}
else
{
size_t x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = 0;
x_104 = lean_usize_of_nat(x_95);
lean_dec(x_95);
lean_inc(x_2);
x_105 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_94, x_103, x_104, x_10, x_2, x_3);
lean_dec(x_94);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_ctor_get(x_91, 4);
lean_inc(x_107);
lean_dec(x_91);
x_108 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_107, x_2, x_106);
return x_108;
}
}
}
default: 
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_109 = lean_ctor_get(x_14, 0);
lean_inc(x_109);
lean_dec(x_14);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_ctor_get(x_110, 2);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lean_Expr_getUsedConstants(x_111);
x_113 = lean_array_get_size(x_112);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_nat_dec_lt(x_114, x_113);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_2);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_10);
lean_ctor_set(x_116, 1, x_3);
return x_116;
}
else
{
uint8_t x_117; 
x_117 = lean_nat_dec_le(x_113, x_113);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_2);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_10);
lean_ctor_set(x_118, 1, x_3);
return x_118;
}
else
{
size_t x_119; size_t x_120; lean_object* x_121; 
x_119 = 0;
x_120 = lean_usize_of_nat(x_113);
lean_dec(x_113);
x_121 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_112, x_119, x_120, x_10, x_2, x_3);
lean_dec(x_112);
return x_121;
}
}
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_3);
x_122 = lean_box(0);
lean_inc(x_1);
x_123 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_1, x_122);
lean_inc(x_5);
lean_inc(x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_5);
lean_inc(x_1);
lean_inc(x_2);
x_125 = lean_environment_find(x_2, x_1);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
switch (lean_obj_tag(x_127)) {
case 0:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_2);
x_128 = lean_array_push(x_5, x_1);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_122);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
case 1:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
lean_dec(x_127);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 2);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Lean_Expr_getUsedConstants(x_133);
x_135 = lean_array_get_size(x_134);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_lt(x_136, x_135);
if (x_137 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
x_138 = x_124;
goto block_149;
}
else
{
uint8_t x_150; 
x_150 = lean_nat_dec_le(x_135, x_135);
if (x_150 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
x_138 = x_124;
goto block_149;
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; lean_object* x_154; 
x_151 = 0;
x_152 = lean_usize_of_nat(x_135);
lean_dec(x_135);
lean_inc(x_2);
x_153 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_134, x_151, x_152, x_122, x_2, x_124);
lean_dec(x_134);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_138 = x_154;
goto block_149;
}
}
block_149:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_131, 1);
lean_inc(x_139);
lean_dec(x_131);
x_140 = l_Lean_Expr_getUsedConstants(x_139);
x_141 = lean_array_get_size(x_140);
x_142 = lean_nat_dec_lt(x_136, x_141);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_2);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_122);
lean_ctor_set(x_143, 1, x_138);
return x_143;
}
else
{
uint8_t x_144; 
x_144 = lean_nat_dec_le(x_141, x_141);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_2);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_122);
lean_ctor_set(x_145, 1, x_138);
return x_145;
}
else
{
size_t x_146; size_t x_147; lean_object* x_148; 
x_146 = 0;
x_147 = lean_usize_of_nat(x_141);
lean_dec(x_141);
x_148 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_140, x_146, x_147, x_122, x_2, x_138);
lean_dec(x_140);
return x_148;
}
}
}
}
case 2:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_155 = lean_ctor_get(x_127, 0);
lean_inc(x_155);
lean_dec(x_127);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_156, 2);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_Expr_getUsedConstants(x_157);
x_159 = lean_array_get_size(x_158);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_nat_dec_lt(x_160, x_159);
if (x_161 == 0)
{
lean_dec(x_159);
lean_dec(x_158);
x_162 = x_124;
goto block_173;
}
else
{
uint8_t x_174; 
x_174 = lean_nat_dec_le(x_159, x_159);
if (x_174 == 0)
{
lean_dec(x_159);
lean_dec(x_158);
x_162 = x_124;
goto block_173;
}
else
{
size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; 
x_175 = 0;
x_176 = lean_usize_of_nat(x_159);
lean_dec(x_159);
lean_inc(x_2);
x_177 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_158, x_175, x_176, x_122, x_2, x_124);
lean_dec(x_158);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_162 = x_178;
goto block_173;
}
}
block_173:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_155, 1);
lean_inc(x_163);
lean_dec(x_155);
x_164 = l_Lean_Expr_getUsedConstants(x_163);
x_165 = lean_array_get_size(x_164);
x_166 = lean_nat_dec_lt(x_160, x_165);
if (x_166 == 0)
{
lean_object* x_167; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_2);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_122);
lean_ctor_set(x_167, 1, x_162);
return x_167;
}
else
{
uint8_t x_168; 
x_168 = lean_nat_dec_le(x_165, x_165);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_2);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_122);
lean_ctor_set(x_169, 1, x_162);
return x_169;
}
else
{
size_t x_170; size_t x_171; lean_object* x_172; 
x_170 = 0;
x_171 = lean_usize_of_nat(x_165);
lean_dec(x_165);
x_172 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_164, x_170, x_171, x_122, x_2, x_162);
lean_dec(x_164);
return x_172;
}
}
}
}
case 3:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_179 = lean_ctor_get(x_127, 0);
lean_inc(x_179);
lean_dec(x_127);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 2);
lean_inc(x_181);
lean_dec(x_180);
x_182 = l_Lean_Expr_getUsedConstants(x_181);
x_183 = lean_array_get_size(x_182);
x_184 = lean_unsigned_to_nat(0u);
x_185 = lean_nat_dec_lt(x_184, x_183);
if (x_185 == 0)
{
lean_dec(x_183);
lean_dec(x_182);
x_186 = x_124;
goto block_197;
}
else
{
uint8_t x_198; 
x_198 = lean_nat_dec_le(x_183, x_183);
if (x_198 == 0)
{
lean_dec(x_183);
lean_dec(x_182);
x_186 = x_124;
goto block_197;
}
else
{
size_t x_199; size_t x_200; lean_object* x_201; lean_object* x_202; 
x_199 = 0;
x_200 = lean_usize_of_nat(x_183);
lean_dec(x_183);
lean_inc(x_2);
x_201 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_182, x_199, x_200, x_122, x_2, x_124);
lean_dec(x_182);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_186 = x_202;
goto block_197;
}
}
block_197:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_179, 1);
lean_inc(x_187);
lean_dec(x_179);
x_188 = l_Lean_Expr_getUsedConstants(x_187);
x_189 = lean_array_get_size(x_188);
x_190 = lean_nat_dec_lt(x_184, x_189);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_2);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_122);
lean_ctor_set(x_191, 1, x_186);
return x_191;
}
else
{
uint8_t x_192; 
x_192 = lean_nat_dec_le(x_189, x_189);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_2);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_122);
lean_ctor_set(x_193, 1, x_186);
return x_193;
}
else
{
size_t x_194; size_t x_195; lean_object* x_196; 
x_194 = 0;
x_195 = lean_usize_of_nat(x_189);
lean_dec(x_189);
x_196 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_188, x_194, x_195, x_122, x_2, x_186);
lean_dec(x_188);
return x_196;
}
}
}
}
case 4:
{
lean_object* x_203; 
lean_dec(x_127);
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_122);
lean_ctor_set(x_203, 1, x_124);
return x_203;
}
case 5:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_204 = lean_ctor_get(x_127, 0);
lean_inc(x_204);
lean_dec(x_127);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_205, 2);
lean_inc(x_206);
lean_dec(x_205);
x_207 = l_Lean_Expr_getUsedConstants(x_206);
x_208 = lean_array_get_size(x_207);
x_209 = lean_unsigned_to_nat(0u);
x_210 = lean_nat_dec_lt(x_209, x_208);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_208);
lean_dec(x_207);
x_211 = lean_ctor_get(x_204, 4);
lean_inc(x_211);
lean_dec(x_204);
x_212 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_211, x_2, x_124);
return x_212;
}
else
{
uint8_t x_213; 
x_213 = lean_nat_dec_le(x_208, x_208);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_208);
lean_dec(x_207);
x_214 = lean_ctor_get(x_204, 4);
lean_inc(x_214);
lean_dec(x_204);
x_215 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_214, x_2, x_124);
return x_215;
}
else
{
size_t x_216; size_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = 0;
x_217 = lean_usize_of_nat(x_208);
lean_dec(x_208);
lean_inc(x_2);
x_218 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_207, x_216, x_217, x_122, x_2, x_124);
lean_dec(x_207);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = lean_ctor_get(x_204, 4);
lean_inc(x_220);
lean_dec(x_204);
x_221 = l_List_forM___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_220, x_2, x_219);
return x_221;
}
}
}
default: 
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_222 = lean_ctor_get(x_127, 0);
lean_inc(x_222);
lean_dec(x_127);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_ctor_get(x_223, 2);
lean_inc(x_224);
lean_dec(x_223);
x_225 = l_Lean_Expr_getUsedConstants(x_224);
x_226 = lean_array_get_size(x_225);
x_227 = lean_unsigned_to_nat(0u);
x_228 = lean_nat_dec_lt(x_227, x_226);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_2);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_122);
lean_ctor_set(x_229, 1, x_124);
return x_229;
}
else
{
uint8_t x_230; 
x_230 = lean_nat_dec_le(x_226, x_226);
if (x_230 == 0)
{
lean_object* x_231; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_2);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_122);
lean_ctor_set(x_231, 1, x_124);
return x_231;
}
else
{
size_t x_232; size_t x_233; lean_object* x_234; 
x_232 = 0;
x_233 = lean_usize_of_nat(x_226);
lean_dec(x_226);
x_234 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_225, x_232, x_233, x_122, x_2, x_124);
lean_dec(x_225);
return x_234;
}
}
}
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_235 = lean_box(0);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_3);
return x_236;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
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
x_1 = lean_mk_string_from_bytes("' depends on axioms: ", 21);
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
x_1 = lean_mk_string_from_bytes("' does not depend on any axioms", 31);
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
x_21 = l_List_mapTR_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(x_19, x_20);
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
x_27 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_25, x_26, x_2, x_3, x_7);
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
x_34 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_32, x_33, x_2, x_3, x_7);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1;
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
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2;
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
x_1 = lean_mk_string_from_bytes("printAxioms", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrintAxioms___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = l_Lean_Elab_Command_elabPrint___closed__2;
x_3 = l_Lean_Elab_Command_elabPrint___closed__3;
x_4 = l_Lean_Elab_Command_elabPrintAxioms___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
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
x_19 = l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(x_11, x_12, x_2, x_3, x_15);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get(x_2, 3);
x_31 = lean_ctor_get(x_2, 4);
x_32 = lean_ctor_get(x_2, 5);
x_33 = lean_ctor_get(x_2, 7);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_30);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
lean_ctor_set(x_34, 6, x_16);
lean_ctor_set(x_34, 7, x_33);
lean_inc(x_3);
lean_inc(x_34);
x_35 = l_Lean_Elab_resolveGlobalConstWithInfos___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(x_11, x_12, x_34, x_3, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(x_36, x_34, x_3, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_34);
lean_dec(x_3);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
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
x_1 = lean_mk_string_from_bytes("elabPrintAxioms", 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1;
x_3 = l_Lean_Elab_Command_elabPrint___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
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
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__4;
x_3 = l_Lean_Elab_Command_elabPrintAxioms___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(124u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__1;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(124u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(124u);
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__4;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__5;
x_4 = lean_unsigned_to_nat(57u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Print(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
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
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7);
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
l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__1 = _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__1);
l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__2 = _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__7___closed__2);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__1 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__1);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__2 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__2);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__3 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__5 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__5);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__6 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__6);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__7 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__7);
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
res = l___regBuiltin_Lean_Elab_Command_elabPrint(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange(lean_io_mk_world());
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
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2);
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
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
