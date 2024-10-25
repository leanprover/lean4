// Lean compiler output
// Module: Lean.Elab.Print
// Imports: Lean.Meta.Eqns Lean.Util.CollectAxioms Lean.Elab.Command
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
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_withSetOptionIn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectAxioms_collect(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__5;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__4;
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintEqns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__7;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__7;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__4;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__4;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__8;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11;
static lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__1;
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__6;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__8;
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18;
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Command_expandDeclId___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__3;
static lean_object* l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__3;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6;
lean_object* l_Lean_getStructureInfo_x3f(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__7;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__6;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__6;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__1;
static lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__2;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrintAxioms___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__5;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__11;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__5;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1;
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___lambda__1(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__6;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
static lean_object* l_Lean_Elab_Command_elabPrint___closed__7;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__4;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20;
lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4;
uint8_t l_Lean_isPrivateName(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__6;
lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
extern lean_object* l_Lean_protectedExt;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__3;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintEqns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__1;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1(lean_object*);
static lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6;
static lean_object* l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15;
lean_object* l_List_mapTR_loop___at_Lean_compileDecl___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1(lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__3;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabPrint___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__8;
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown identifier '", 20, 20);
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
x_1 = lean_mk_string_unchecked("'", 1, 1);
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
x_7 = l_Lean_MessageData_ofExpr(x_6);
x_8 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__2;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_11 = lean_alloc_ctor(7, 2, 0);
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
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_2);
x_7 = l_Lean_MessageData_ofName(x_4);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_1 = x_5;
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_MessageData_ofName(x_10);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_1 = x_11;
x_2 = x_15;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".{", 2, 2);
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
x_1 = lean_mk_string_unchecked("}", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__8;
x_2 = l_Lean_MessageData_ofFormat(x_1);
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_MessageData_ofName(x_4);
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_7);
x_8 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1(x_5, x_9);
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_MessageData_ofName(x_13);
x_16 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__5;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___spec__1(x_14, x_19);
x_21 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__9;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
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
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("private ", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("protected ", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__12;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsafe ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__15;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partial ", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__17;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__18;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@[reducible] ", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__21;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@[irreducible] ", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__23;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__24;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_193; 
lean_inc(x_2);
x_9 = l_Lean_getReducibilityStatus___at___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___spec__1(x_2, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = lean_st_ref_get(x_7, x_11);
x_193 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_193) {
case 0:
{
lean_object* x_194; 
x_194 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__22;
x_14 = x_194;
goto block_192;
}
case 1:
{
lean_object* x_195; 
x_195 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
x_14 = x_195;
goto block_192;
}
default: 
{
lean_object* x_196; 
x_196 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__25;
x_14 = x_196;
goto block_192;
}
}
block_192:
{
lean_object* x_15; 
switch (x_5) {
case 0:
{
lean_object* x_189; 
x_189 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__16;
x_15 = x_189;
goto block_188;
}
case 1:
{
lean_object* x_190; 
x_190 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
x_15 = x_190;
goto block_188;
}
default: 
{
lean_object* x_191; 
x_191 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__19;
x_15 = x_191;
goto block_188;
}
}
block_188:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_13, 0);
if (lean_is_scalar(x_12)) {
 x_18 = lean_alloc_ctor(7, 2, 0);
} else {
 x_18 = x_12;
 lean_ctor_set_tag(x_18, 7);
}
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
lean_inc(x_2);
x_21 = l_Lean_TagDeclarationExtension_isTagged(x_20, x_19, x_2);
lean_dec(x_19);
lean_inc(x_2);
x_22 = lean_private_to_user_name(x_2);
if (x_21 == 0)
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofName(x_2);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_MessageData_ofExpr(x_4);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_13, 0, x_35);
return x_13;
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 0, x_1);
x_40 = l_Lean_MessageData_ofFormat(x_22);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_MessageData_ofName(x_37);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_ofExpr(x_4);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_13, 0, x_51);
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_52 = lean_ctor_get(x_22, 0);
lean_inc(x_52);
lean_dec(x_22);
x_53 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_18);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_1);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_MessageData_ofName(x_52);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_MessageData_ofExpr(x_4);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_13, 0, x_67);
return x_13;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_18);
lean_ctor_set(x_69, 1, x_68);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_1);
x_71 = l_Lean_MessageData_ofFormat(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_MessageData_ofName(x_2);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_MessageData_ofExpr(x_4);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_13, 0, x_82);
return x_13;
}
else
{
uint8_t x_83; 
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_22);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_84 = lean_ctor_get(x_22, 0);
x_85 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_69);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_tag(x_22, 3);
lean_ctor_set(x_22, 0, x_1);
x_87 = l_Lean_MessageData_ofFormat(x_22);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_MessageData_ofName(x_84);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_MessageData_ofExpr(x_4);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_13, 0, x_98);
return x_13;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_99 = lean_ctor_get(x_22, 0);
lean_inc(x_99);
lean_dec(x_22);
x_100 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_69);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_1);
x_103 = l_Lean_MessageData_ofFormat(x_102);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_MessageData_ofName(x_99);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_MessageData_ofExpr(x_4);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_13, 0, x_114);
return x_13;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_13, 0);
x_116 = lean_ctor_get(x_13, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_13);
if (lean_is_scalar(x_12)) {
 x_117 = lean_alloc_ctor(7, 2, 0);
} else {
 x_117 = x_12;
 lean_ctor_set_tag(x_117, 7);
}
lean_ctor_set(x_117, 0, x_14);
lean_ctor_set(x_117, 1, x_15);
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
lean_dec(x_115);
x_119 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
lean_inc(x_2);
x_120 = l_Lean_TagDeclarationExtension_isTagged(x_119, x_118, x_2);
lean_dec(x_118);
lean_inc(x_2);
x_121 = lean_private_to_user_name(x_2);
if (x_120 == 0)
{
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_122 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_122, 0, x_1);
x_123 = l_Lean_MessageData_ofFormat(x_122);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_117);
lean_ctor_set(x_124, 1, x_123);
x_125 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_MessageData_ofName(x_2);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_MessageData_ofExpr(x_4);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_116);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_2);
x_136 = lean_ctor_get(x_121, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_137 = x_121;
} else {
 lean_dec_ref(x_121);
 x_137 = lean_box(0);
}
x_138 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_117);
lean_ctor_set(x_139, 1, x_138);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(3, 1, 0);
} else {
 x_140 = x_137;
 lean_ctor_set_tag(x_140, 3);
}
lean_ctor_set(x_140, 0, x_1);
x_141 = l_Lean_MessageData_ofFormat(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_MessageData_ofName(x_136);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_MessageData_ofExpr(x_4);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_116);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__13;
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_117);
lean_ctor_set(x_155, 1, x_154);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_156 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_156, 0, x_1);
x_157 = l_Lean_MessageData_ofFormat(x_156);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
x_159 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_MessageData_ofName(x_2);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_MessageData_ofExpr(x_4);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_116);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_2);
x_170 = lean_ctor_get(x_121, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_171 = x_121;
} else {
 lean_dec_ref(x_121);
 x_171 = lean_box(0);
}
x_172 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_155);
lean_ctor_set(x_173, 1, x_172);
if (lean_is_scalar(x_171)) {
 x_174 = lean_alloc_ctor(3, 1, 0);
} else {
 x_174 = x_171;
 lean_ctor_set_tag(x_174, 3);
}
lean_ctor_set(x_174, 0, x_1);
x_175 = l_Lean_MessageData_ofFormat(x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_175);
x_177 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_MessageData_ofName(x_170);
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData(x_3);
x_182 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_MessageData_ofExpr(x_4);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_116);
return x_187;
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
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" :=", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_13);
x_14 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_MessageData_ofExpr(x_5);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = 0;
x_19 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_17, x_18, x_7, x_8, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__3;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_ofExpr(x_5);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = 0;
x_29 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_27, x_28, x_7, x_8, x_21);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_8);
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
lean_dec(x_7);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Quotient primitive", 18, 18);
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
lean_dec(x_5);
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_9);
x_11 = l_Lean_getConstInfo___at_Lean_Elab_Command_expandDeclId___spec__9(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_3);
x_14 = l_Lean_MessageData_ofName(x_9);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_ConstantInfo_type(x_12);
lean_dec(x_12);
x_19 = l_Lean_MessageData_ofExpr(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_2 = x_10;
x_3 = x_20;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_22; 
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_4);
lean_inc(x_26);
x_28 = l_Lean_getConstInfo___at_Lean_Elab_Command_expandDeclId___spec__9(x_26, x_4, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_1);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_1);
x_32 = l_Lean_MessageData_ofName(x_26);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_ConstantInfo_type(x_29);
lean_dec(x_29);
x_37 = l_Lean_MessageData_ofExpr(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_2 = x_27;
x_3 = x_38;
x_6 = x_30;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
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
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inductive", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("number of parameters: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constructors:", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1;
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(x_10, x_1, x_2, x_4, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_14);
x_15 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
x_22 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_inc(x_7);
x_24 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(x_14, x_5, x_23, x_7, x_8, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 0;
x_28 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_25, x_27, x_7, x_8, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_MessageData_ofFormat(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
x_44 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__7;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_7);
x_46 = l_List_forIn_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(x_35, x_5, x_45, x_7, x_8, x_34);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 0;
x_50 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_47, x_49, x_7, x_8, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_7);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
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
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_param___override(x_5);
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
x_11 = l_Lean_Level_param___override(x_9);
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
static lean_object* _init_l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Print", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.Print.0.Lean.Elab.Command.printStructure.doFields", 68, 68);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("missing structure field info", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__1;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__2;
x_3 = lean_unsigned_to_nat(92u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; uint8_t x_25; 
x_16 = lean_array_uget(x_3, x_5);
x_24 = lean_st_ref_get(x_12, x_13);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_16);
lean_inc(x_1);
x_29 = l_Lean_getProjFnForField_x3f(x_28, x_1, x_16);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_24);
lean_dec(x_16);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__4;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2(x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_6);
x_17 = x_33;
x_18 = x_32;
goto block_23;
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
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
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = l_Lean_isPrivateName(x_39);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = 1;
x_42 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5;
x_43 = l_Lean_Name_toString(x_16, x_41, x_42);
lean_ctor_set_tag(x_29, 3);
lean_ctor_set(x_29, 0, x_43);
lean_inc(x_7);
x_44 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_ConstantInfo_type(x_45);
lean_dec(x_45);
x_48 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_49 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_48, x_47, x_9, x_10, x_11, x_12, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_52);
lean_ctor_set(x_24, 0, x_6);
x_53 = l_Lean_MessageData_ofFormat(x_29);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_24);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_MessageData_ofExpr(x_50);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_17 = x_59;
x_18 = x_51;
goto block_23;
}
else
{
uint8_t x_60; 
lean_dec(x_29);
lean_free_object(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_49);
if (x_60 == 0)
{
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_49, 0);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_49);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_29);
lean_free_object(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_44);
if (x_64 == 0)
{
return x_44;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_44, 0);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_44);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = 1;
x_69 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5;
x_70 = l_Lean_Name_toString(x_16, x_68, x_69);
lean_ctor_set_tag(x_29, 3);
lean_ctor_set(x_29, 0, x_70);
x_71 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
lean_ctor_set_tag(x_24, 5);
lean_ctor_set(x_24, 1, x_29);
lean_ctor_set(x_24, 0, x_71);
lean_inc(x_7);
x_72 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_ConstantInfo_type(x_73);
lean_dec(x_73);
x_76 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_77 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_76, x_75, x_9, x_10, x_11, x_12, x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_6);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_MessageData_ofFormat(x_24);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_MessageData_ofExpr(x_78);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_17 = x_88;
x_18 = x_79;
goto block_23;
}
else
{
uint8_t x_89; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_77);
if (x_89 == 0)
{
return x_77;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_77, 0);
x_91 = lean_ctor_get(x_77, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_77);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_72);
if (x_93 == 0)
{
return x_72;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_72, 0);
x_95 = lean_ctor_get(x_72, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_72);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_29, 0);
lean_inc(x_97);
lean_dec(x_29);
x_98 = l_Lean_isPrivateName(x_97);
if (x_98 == 0)
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = 1;
x_100 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5;
x_101 = l_Lean_Name_toString(x_16, x_99, x_100);
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_101);
lean_inc(x_7);
x_103 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_97, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_ConstantInfo_type(x_104);
lean_dec(x_104);
x_107 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_108 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_107, x_106, x_9, x_10, x_11, x_12, x_105);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_111);
lean_ctor_set(x_24, 0, x_6);
x_112 = l_Lean_MessageData_ofFormat(x_102);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_24);
lean_ctor_set(x_113, 1, x_112);
x_114 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_MessageData_ofExpr(x_109);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_17 = x_118;
x_18 = x_110;
goto block_23;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_102);
lean_free_object(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_119 = lean_ctor_get(x_108, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_108, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_121 = x_108;
} else {
 lean_dec_ref(x_108);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_102);
lean_free_object(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_123 = lean_ctor_get(x_103, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_103, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_125 = x_103;
} else {
 lean_dec_ref(x_103);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = 1;
x_128 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5;
x_129 = l_Lean_Name_toString(x_16, x_127, x_128);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
lean_ctor_set_tag(x_24, 5);
lean_ctor_set(x_24, 1, x_130);
lean_ctor_set(x_24, 0, x_131);
lean_inc(x_7);
x_132 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_97, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_ConstantInfo_type(x_133);
lean_dec(x_133);
x_136 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_137 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_136, x_135, x_9, x_10, x_11, x_12, x_134);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_6);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_MessageData_ofFormat(x_24);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_MessageData_ofExpr(x_138);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_17 = x_148;
x_18 = x_139;
goto block_23;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_149 = lean_ctor_get(x_137, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_151 = x_137;
} else {
 lean_dec_ref(x_137);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_153 = lean_ctor_get(x_132, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_132, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_155 = x_132;
} else {
 lean_dec_ref(x_132);
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
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_24, 0);
x_158 = lean_ctor_get(x_24, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_24);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
lean_inc(x_16);
lean_inc(x_1);
x_160 = l_Lean_getProjFnForField_x3f(x_159, x_1, x_16);
lean_dec(x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_16);
x_161 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__4;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_162 = l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2(x_161, x_7, x_8, x_9, x_10, x_11, x_12, x_158);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_6);
x_17 = x_164;
x_18 = x_163;
goto block_23;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_167 = x_162;
} else {
 lean_dec_ref(x_162);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_160, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_170 = x_160;
} else {
 lean_dec_ref(x_160);
 x_170 = lean_box(0);
}
x_171 = l_Lean_isPrivateName(x_169);
if (x_171 == 0)
{
uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = 1;
x_173 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5;
x_174 = l_Lean_Name_toString(x_16, x_172, x_173);
if (lean_is_scalar(x_170)) {
 x_175 = lean_alloc_ctor(3, 1, 0);
} else {
 x_175 = x_170;
 lean_ctor_set_tag(x_175, 3);
}
lean_ctor_set(x_175, 0, x_174);
lean_inc(x_7);
x_176 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_169, x_7, x_8, x_9, x_10, x_11, x_12, x_158);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = l_Lean_ConstantInfo_type(x_177);
lean_dec(x_177);
x_180 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_181 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_180, x_179, x_9, x_10, x_11, x_12, x_178);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_6);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_Lean_MessageData_ofFormat(x_175);
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_MessageData_ofExpr(x_182);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_17 = x_192;
x_18 = x_183;
goto block_23;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_175);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_193 = lean_ctor_get(x_181, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_181, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_195 = x_181;
} else {
 lean_dec_ref(x_181);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_175);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_197 = lean_ctor_get(x_176, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_176, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_199 = x_176;
} else {
 lean_dec_ref(x_176);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = 1;
x_202 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5;
x_203 = l_Lean_Name_toString(x_16, x_201, x_202);
if (lean_is_scalar(x_170)) {
 x_204 = lean_alloc_ctor(3, 1, 0);
} else {
 x_204 = x_170;
 lean_ctor_set_tag(x_204, 3);
}
lean_ctor_set(x_204, 0, x_203);
x_205 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
x_206 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
lean_inc(x_7);
x_207 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_169, x_7, x_8, x_9, x_10, x_11, x_12, x_158);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l_Lean_ConstantInfo_type(x_208);
lean_dec(x_208);
x_211 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_212 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_211, x_210, x_9, x_10, x_11, x_12, x_209);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_6);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_MessageData_ofFormat(x_206);
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_MessageData_ofExpr(x_213);
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_17 = x_223;
x_18 = x_214;
goto block_23;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_206);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_224 = lean_ctor_get(x_212, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_212, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_226 = x_212;
} else {
 lean_dec_ref(x_212);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_206);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_228 = lean_ctor_get(x_207, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_207, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_230 = x_207;
} else {
 lean_dec_ref(x_207);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
x_13 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg___lambda__1), 10, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
x_12 = lean_box(0);
x_13 = 0;
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_13, x_12, x_1, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_push(x_1, x_4);
x_13 = lean_array_size(x_2);
x_14 = 0;
x_15 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__3;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3(x_3, x_12, x_2, x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_17, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("self", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_box(0);
x_14 = l_List_mapTR_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__1(x_1, x_13);
lean_inc(x_2);
x_15 = l_Lean_Expr_const___override(x_2, x_14);
x_16 = l_Lean_mkAppN(x_15, x_4);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__1___boxed), 11, 3);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_2);
x_18 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__2;
x_19 = 0;
x_20 = 0;
x_21 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(x_18, x_19, x_16, x_17, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_ConstantInfo_type(x_12);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___boxed), 12, 3);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_3);
x_16 = 0;
x_17 = l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg(x_14, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__3), 10, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
x_8 = l_Lean_Elab_Command_liftTermElabM___rarg(x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__4___rarg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constructor:", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fields:", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structure", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("class", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
if (x_8 == 0)
{
lean_object* x_96; 
x_96 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__7;
x_12 = x_96;
goto block_95;
}
else
{
lean_object* x_97; 
x_97 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__8;
x_12 = x_97;
goto block_95;
}
block_95:
{
lean_object* x_13; uint8_t x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_x27(x_12, x_1, x_2, x_4, x_7, x_9, x_10, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_16);
x_17 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
x_24 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__3;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_9);
lean_inc(x_5);
x_26 = l_Lean_getConstInfo___at_Lean_Elab_Command_expandDeclId___spec__9(x_5, x_9, x_10, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_16);
x_30 = l_Lean_MessageData_ofName(x_5);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_ConstantInfo_type(x_27);
lean_dec(x_27);
x_35 = l_Lean_MessageData_ofExpr(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields(x_1, x_2, x_6, x_9, x_10, x_28);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_16);
x_41 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__6;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
x_44 = 0;
x_45 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_43, x_44, x_9, x_10, x_39);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_36);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 0);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_37);
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
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_26);
if (x_50 == 0)
{
return x_26;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_26, 0);
x_52 = lean_ctor_get(x_26, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_26);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_MessageData_ofFormat(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_56);
x_65 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__3;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_9);
lean_inc(x_5);
x_67 = l_Lean_getConstInfo___at_Lean_Elab_Command_expandDeclId___spec__9(x_5, x_9, x_10, x_55);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_56);
x_71 = l_Lean_MessageData_ofName(x_5);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_ConstantInfo_type(x_68);
lean_dec(x_68);
x_76 = l_Lean_MessageData_ofExpr(x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields(x_1, x_2, x_6, x_9, x_10, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_56);
x_82 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__6;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
x_85 = 0;
x_86 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_84, x_85, x_9, x_10, x_80);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_77);
lean_dec(x_9);
x_87 = lean_ctor_get(x_78, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_78, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_89 = x_78;
} else {
 lean_dec_ref(x_78);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_ctor_get(x_67, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_67, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_93 = x_67;
} else {
 lean_dec_ref(x_67);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = lean_unbox(x_8);
lean_dec(x_8);
x_14 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure(x_1, x_2, x_3, x_4, x_5, x_6, x_12, x_13, x_9, x_10, x_11);
lean_dec(x_10);
return x_14;
}
}
static lean_object* _init_l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedCommandElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1___closed__1;
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_3(x_6, x_2, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("axiom", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("theorem", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("opaque", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.Print.0.Lean.Elab.Command.printIdCore", 56, 56);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structures have only one constructor", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__1;
x_2 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5;
x_3 = lean_unsigned_to_nat(108u);
x_4 = lean_unsigned_to_nat(28u);
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constructor", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recursor", 8, 8);
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
lean_inc(x_8);
x_9 = lean_environment_find(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
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
lean_dec(x_8);
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
lean_dec(x_3);
return x_18;
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
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
lean_dec(x_3);
return x_26;
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_8);
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
lean_dec(x_3);
return x_34;
}
case 3:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
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
lean_dec(x_3);
return x_41;
}
case 4:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_dec(x_8);
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
lean_dec(x_3);
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
x_53 = lean_ctor_get_uint8(x_49, sizeof(void*)*6 + 1);
lean_dec(x_49);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 2);
lean_inc(x_55);
lean_dec(x_50);
lean_inc(x_1);
x_56 = l_Lean_getStructureInfo_x3f(x_8, x_1);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_8);
x_57 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(x_1, x_54, x_51, x_55, x_52, x_53, x_2, x_3, x_7);
lean_dec(x_3);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_1);
x_59 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__7;
x_60 = l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1(x_59, x_2, x_3, x_7);
return x_60;
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
lean_dec(x_52);
lean_inc(x_1);
x_64 = lean_is_class(x_8, x_1);
x_65 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure(x_1, x_54, x_51, x_55, x_63, x_62, x_53, x_64, x_2, x_3, x_7);
lean_dec(x_3);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_1);
x_66 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__7;
x_67 = l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1(x_66, x_2, x_3, x_7);
return x_67;
}
}
}
}
case 6:
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_8);
x_68 = lean_ctor_get(x_11, 0);
lean_inc(x_68);
lean_dec(x_11);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_68, sizeof(void*)*5);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 2);
lean_inc(x_72);
lean_dec(x_69);
x_73 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__8;
x_74 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_73, x_1, x_71, x_72, x_70, x_2, x_3, x_7);
lean_dec(x_3);
return x_74;
}
default: 
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_8);
x_75 = lean_ctor_get(x_11, 0);
lean_inc(x_75);
lean_dec(x_11);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_75, sizeof(void*)*7 + 1);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 2);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__9;
x_81 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_80, x_1, x_78, x_79, x_77, x_2, x_3, x_7);
lean_dec(x_3);
return x_81;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__4;
x_3 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__3;
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
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__2;
x_2 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = lean_box(0);
x_7 = 0;
x_8 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___closed__6;
lean_inc(x_1);
x_9 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_7);
x_10 = l_Lean_Elab_addCompletionInfo___at_Lean_withSetOptionIn___spec__2(x_9, x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstWithInfos), 5, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_6);
x_13 = l_Lean_Elab_Command_liftCoreM___rarg(x_12, x_2, x_3, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_List_forM___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(x_14, x_2, x_3, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("print", 5, 5);
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
x_1 = lean_mk_string_unchecked("invalid #print command", 22, 22);
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
x_1 = lean_mk_string_unchecked("ident", 5, 5);
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
x_1 = lean_mk_string_unchecked("str", 3, 3);
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
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_MessageData_ofFormat(x_20);
x_22 = 0;
x_23 = l_Lean_logAt___at_Lean_Elab_Command_elabCommand___spec__4(x_10, x_21, x_22, x_2, x_3, x_4);
lean_dec(x_3);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
x_35 = lean_ctor_get(x_2, 4);
x_36 = lean_ctor_get(x_2, 5);
x_37 = lean_ctor_get(x_2, 7);
x_38 = lean_ctor_get(x_2, 8);
x_39 = lean_ctor_get(x_2, 9);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_36);
lean_ctor_set(x_41, 6, x_27);
lean_ctor_set(x_41, 7, x_37);
lean_ctor_set(x_41, 8, x_38);
lean_ctor_set(x_41, 9, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*10, x_40);
x_42 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(x_12, x_41, x_3, x_26);
return x_42;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabPrint", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1;
x_3 = l_Lean_Elab_Command_elabPrint___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrint), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__4;
x_3 = l_Lean_Elab_Command_elabPrint___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(118u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(121u);
x_2 = lean_unsigned_to_nat(66u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(66u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(118u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(118u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(45u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__2;
x_10 = l_Lean_CollectAxioms_collect(x_1, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__2;
x_17 = l_Lean_CollectAxioms_collect(x_1, x_15, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
static lean_object* _init_l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_lt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2___closed__1;
lean_inc(x_2);
x_6 = l_Array_qpartition___rarg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' depends on axioms: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not depend on any axioms", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Array_isEmpty___rarg(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_10 = l_Lean_MessageData_ofName(x_1);
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_10);
lean_ctor_set(x_5, 0, x_11);
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_get_size(x_7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_14, x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2(x_7, x_17, x_16);
lean_dec(x_16);
x_19 = lean_array_to_list(x_18);
x_20 = lean_box(0);
x_21 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_19, x_20);
x_22 = l_Lean_MessageData_ofList(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = 0;
x_27 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_25, x_26, x_2, x_3, x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_7);
x_28 = l_Lean_MessageData_ofName(x_1);
x_29 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_29);
x_30 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_30);
x_32 = 0;
x_33 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_31, x_32, x_2, x_3, x_8);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = l_Array_isEmpty___rarg(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_37 = l_Lean_MessageData_ofName(x_1);
x_38 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_get_size(x_34);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_42, x_43);
lean_dec(x_42);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2(x_34, x_45, x_44);
lean_dec(x_44);
x_47 = lean_array_to_list(x_46);
x_48 = lean_box(0);
x_49 = l_List_mapTR_loop___at_Lean_compileDecl___spec__1(x_47, x_48);
x_50 = l_Lean_MessageData_ofList(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_levelParamsToMessageData___closed__6;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = 0;
x_55 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_53, x_54, x_2, x_3, x_35);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
lean_dec(x_34);
x_56 = l_Lean_MessageData_ofName(x_1);
x_57 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = 0;
x_62 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_60, x_61, x_2, x_3, x_35);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
x_1 = lean_mk_string_unchecked("printAxioms", 11, 11);
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
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstWithInfos), 5, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_replaceRef(x_9, x_15);
lean_dec(x_15);
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_2, 6);
lean_dec(x_19);
lean_ctor_set(x_2, 6, x_17);
x_20 = l_Lean_Elab_Command_liftCoreM___rarg(x_13, x_2, x_3, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(x_21, x_2, x_3, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_2);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_ctor_get(x_2, 3);
x_32 = lean_ctor_get(x_2, 4);
x_33 = lean_ctor_get(x_2, 5);
x_34 = lean_ctor_get(x_2, 7);
x_35 = lean_ctor_get(x_2, 8);
x_36 = lean_ctor_get(x_2, 9);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 3, x_31);
lean_ctor_set(x_38, 4, x_32);
lean_ctor_set(x_38, 5, x_33);
lean_ctor_set(x_38, 6, x_17);
lean_ctor_set(x_38, 7, x_34);
lean_ctor_set(x_38, 8, x_35);
lean_ctor_set(x_38, 9, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*10, x_37);
x_39 = l_Lean_Elab_Command_liftCoreM___rarg(x_13, x_38, x_3, x_16);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(x_40, x_38, x_3, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_38);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
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
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at_Lean_Elab_Command_elabPrintAxioms___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintAxioms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabPrintAxioms(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabPrintAxioms", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1;
x_3 = l_Lean_Elab_Command_elabPrint___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrintAxioms___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__4;
x_3 = l_Lean_Elab_Command_elabPrintAxioms___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(158u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(162u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(158u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(158u);
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(57u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_1, x_3);
lean_inc(x_5);
lean_inc(x_10);
x_11 = l_Lean_getConstInfo___at_Lean_Elab_Command_expandDeclId___spec__9(x_10, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_ConstantInfo_levelParams(x_12);
x_15 = l_Lean_ConstantInfo_type(x_12);
lean_dec(x_12);
x_16 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3;
x_17 = 1;
x_18 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_16, x_10, x_14, x_15, x_17, x_5, x_6, x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_22);
lean_ctor_set(x_18, 0, x_4);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_20);
x_24 = 1;
x_25 = lean_usize_add(x_3, x_24);
x_3 = x_25;
x_4 = x_23;
x_7 = x_21;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__4;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = 1;
x_33 = lean_usize_add(x_3, x_32);
x_3 = x_33;
x_4 = x_31;
x_7 = x_28;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not have equations", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equations:", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lambda__1___boxed), 8, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_Command_liftTermElabM___rarg(x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_MessageData_ofName(x_1);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___closed__4;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = 0;
x_15 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_13, x_14, x_2, x_3, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_array_size(x_17);
x_19 = 0;
x_20 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__4;
lean_inc(x_2);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___spec__1(x_17, x_18, x_19, x_20, x_2, x_3, x_16);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
x_25 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_22, x_24, x_2, x_3, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintEqns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
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
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf(x_7, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstWithInfos), 5, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Elab_Command_liftCoreM___rarg(x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_forM___at_Lean_Elab_Command_elabPrintEqns___spec__1(x_10, x_2, x_3, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
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
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Command_elabPrintEqns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at_Lean_Elab_Command_elabPrintEqns___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabPrintEqns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabPrintEqns(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("printEqns", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = l_Lean_Elab_Command_elabPrint___closed__2;
x_3 = l_Lean_Elab_Command_elabPrint___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabPrintEqns", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1;
x_3 = l_Lean_Elab_Command_elabPrint___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrintEqns___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(173u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(176u);
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(21u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(173u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(173u);
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(40u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(53u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectAxioms(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Print(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectAxioms(builtin, lean_io_mk_world());
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
l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2___closed__1 = _init_l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___spec__3___closed__5);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure_doFields___lambda__2___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__4);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__5 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__5);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__6 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__6);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__7 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__7);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__8 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printStructure___closed__8);
l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1___closed__1 = _init_l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___spec__1___closed__1);
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
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__7 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__7);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__8 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__8);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__9 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__9);
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
l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabPrint__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabPrint_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__1 = _init_l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__1();
lean_mark_persistent(l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__1);
l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__2 = _init_l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__2();
lean_mark_persistent(l_Lean_collectAxioms___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1___closed__2);
l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2___closed__1 = _init_l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__2___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabPrintAxioms___spec__1___rarg___closed__2);
l_Lean_Elab_Command_elabPrintAxioms___closed__1 = _init_l_Lean_Elab_Command_elabPrintAxioms___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabPrintAxioms___closed__1);
l_Lean_Elab_Command_elabPrintAxioms___closed__2 = _init_l_Lean_Elab_Command_elabPrintAxioms___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabPrintAxioms___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printEqnsOf___closed__4);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabPrintEqns__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Command_elabPrintEqns_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
