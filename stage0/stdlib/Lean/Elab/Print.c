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
lean_object* l_Lean_Elab_Command_CollectAxioms_collect_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__2;
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__4;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_Command_elabPrint___closed__6;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__4;
lean_object* l_Lean_Elab_Command_elabPrint___closed__1;
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint(lean_object*);
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_assumption___closed__1;
lean_object* l_List_map___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Command_CollectAxioms_collect_match__2(lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint___closed__4;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__2___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__2;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__2;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms(lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__6;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__9;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__3;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7___closed__8;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CollectAxioms_collect_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__1;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__2;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
lean_object* l_List_forM___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___closed__4;
extern lean_object* l_Lean_protectedExt;
lean_object* l_Lean_Elab_Command_CollectAxioms_State_axioms___default;
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7___closed__6;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_Elab_Command_elabPrintAxioms___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CollectAxioms_collect_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__3;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___closed__2;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3(lean_object*);
lean_object* l_Lean_Elab_Command_CollectAxioms_State_visited___default;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__6;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_resolveGlobalConst___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_match__1(lean_object*);
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__8;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabPrintAxioms___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__5;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(uint8_t);
lean_object* l_Lean_Elab_Command_CollectAxioms_collect(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__3;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__5;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___closed__3;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3;
lean_object* l_Lean_Elab_Command_elabPrintAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore_match__1(lean_object*);
extern lean_object* l_Lean_Elab_Term_resolveName___closed__2;
lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint___closed__3;
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint___closed__5;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabPrintAxioms___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__1;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___boxed(lean_object*);
extern lean_object* l_Lean_Elab_Lean_Elab_DeclModifiers___instance__2___closed__4;
lean_object* l_List_map___main___at_Lean_resolveGlobalConst___spec__2(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1;
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__4;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__2(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_Term_resolveName___closed__2;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_9, x_2, x_3, x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_throwUnknownId(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_Lean_MessageData_arrayExpr_toMessageData___closed__2;
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
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".{");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Lean_Elab_DeclModifiers___instance__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Meta_assumption___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__3;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___spec__1(x_4, x_7);
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__4;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader_match__2___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private ");
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
x_1 = lean_mk_string("protected ");
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
x_1 = lean_mk_string("unsafe ");
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
if (x_5 == 0)
{
lean_object* x_148; 
x_148 = l_Lean_Meta_assumption___closed__1;
x_10 = x_148;
goto block_147;
}
else
{
lean_object* x_149; 
x_149 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__10;
x_10 = x_149;
goto block_147;
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
x_15 = l_Lean_TagDeclarationExtension_isTagged(x_14, x_13, x_2);
lean_dec(x_13);
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
x_20 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(x_3);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
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
x_31 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
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
x_36 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___closed__4;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_30);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(x_3);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
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
x_46 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
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
x_51 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___closed__4;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_2);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(x_3);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
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
x_62 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
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
x_67 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___closed__4;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_69, 0, x_61);
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(x_3);
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
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
x_81 = l_Lean_TagDeclarationExtension_isTagged(x_80, x_79, x_2);
lean_dec(x_79);
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
x_86 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___closed__4;
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_88, 0, x_2);
x_89 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(x_3);
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
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
x_98 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
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
x_103 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___closed__4;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_105, 0, x_97);
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(x_3);
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
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
x_114 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__7;
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
x_119 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___closed__4;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_121, 0, x_2);
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(x_3);
x_124 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
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
x_131 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__4;
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
x_136 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___closed__4;
x_137 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_138, 0, x_130);
x_139 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData(x_3);
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_MessageData_ofList___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_5);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = 0;
x_20 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_18, x_19, x_7, x_8, x_12);
return x_20;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_10, x_12, x_6, x_7, x_11);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1;
x_8 = 0;
x_9 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomLike(x_7, x_1, x_2, x_3, x_8, x_4, x_5, x_6);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot(x_2);
return x_3;
}
}
lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_17, x_2, x_3, x_8);
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
x_27 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_30, x_2, x_3, x_21);
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
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_16 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader___closed__1;
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__1;
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_mkHeader(x_11, x_1, x_2, x_5, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MessageData_ofList___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_8);
x_19 = l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2(x_15, x_6, x_18, x_8, x_9, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
x_23 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_20, x_22, x_8, x_9, x_21);
lean_dec(x_8);
return x_23;
}
else
{
uint8_t x_24; 
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
lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forInAux___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printInduct(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(x_16);
x_21 = lean_apply_4(x_2, x_18, x_19, x_20, x_17);
return x_21;
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 2);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(x_26);
x_31 = lean_apply_6(x_3, x_28, x_29, x_24, x_30, x_27, x_25);
return x_31;
}
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 2);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_apply_4(x_4, x_36, x_37, x_34, x_35);
return x_38;
}
case 3:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_13, 0);
lean_inc(x_39);
lean_dec(x_13);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 2);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_box(x_42);
x_47 = lean_apply_5(x_5, x_44, x_45, x_46, x_43, x_41);
return x_47;
}
case 4:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_ctor_get(x_13, 0);
lean_inc(x_48);
lean_dec(x_13);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 2);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_box(x_50);
x_55 = lean_apply_4(x_6, x_54, x_52, x_53, x_51);
return x_55;
}
case 5:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_ctor_get(x_13, 0);
lean_inc(x_56);
lean_dec(x_13);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 4);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_56, sizeof(void*)*5);
x_63 = lean_ctor_get_uint8(x_56, sizeof(void*)*5 + 1);
x_64 = lean_ctor_get_uint8(x_56, sizeof(void*)*5 + 2);
lean_dec(x_56);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_57, 2);
lean_inc(x_67);
lean_dec(x_57);
x_68 = lean_box(x_63);
x_69 = lean_box(x_62);
x_70 = lean_box(x_64);
x_71 = lean_apply_10(x_9, x_66, x_58, x_59, x_67, x_61, x_68, x_65, x_60, x_69, x_70);
return x_71;
}
case 6:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_ctor_get(x_13, 0);
lean_inc(x_72);
lean_dec(x_13);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 4);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_72, sizeof(void*)*5);
lean_dec(x_72);
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_73, 2);
lean_inc(x_81);
lean_dec(x_73);
x_82 = lean_box(x_78);
x_83 = lean_apply_8(x_7, x_80, x_81, x_82, x_79, x_74, x_75, x_76, x_77);
return x_83;
}
default: 
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_ctor_get(x_13, 0);
lean_inc(x_84);
lean_dec(x_13);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 5);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 6);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_84, sizeof(void*)*7);
x_93 = lean_ctor_get_uint8(x_84, sizeof(void*)*7 + 1);
lean_dec(x_84);
x_94 = lean_ctor_get(x_85, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_85, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_85, 2);
lean_inc(x_96);
lean_dec(x_85);
x_97 = lean_box(x_93);
x_98 = lean_box(x_92);
x_99 = lean_apply_11(x_8, x_95, x_96, x_97, x_94, x_86, x_87, x_88, x_89, x_90, x_91, x_98);
return x_99;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore_match__1___rarg), 10, 0);
return x_2;
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec(x_2);
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
lean_dec(x_2);
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
x_33 = 0;
x_34 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike(x_32, x_1, x_30, x_31, x_29, x_33, x_2, x_3, x_7);
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_dec(x_2);
lean_dec(x_68);
return x_71;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printIdCore(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 4);
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
x_20 = lean_ctor_get(x_18, 4);
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
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = l_Lean_mkConst(x_1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_11, x_2, x_3, x_4);
return x_12;
}
}
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_List_map___main___at_Lean_resolveGlobalConst___spec__2(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_List_filterAux___main___at_Lean_resolveGlobalConst___spec__1(x_6, x_8);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1(x_9, x_11, x_2, x_3, x_7);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_9);
x_13 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___rarg(x_1, x_2, x_3, x_7);
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
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_List_forM___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(x_6, x_2, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabPrint_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabPrint_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrint_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid #print command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabPrint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getNumArgs(x_1);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_Elab_Command_elabPrint___closed__3;
x_9 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_8, x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Syntax_isIdent(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Syntax_isStrLit_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_Command_elabPrint___closed__6;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___rarg(x_14, x_2, x_3, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = 0;
x_20 = l_Lean_Elab_log___at_Lean_Elab_Command_logUnknownDecl___spec__1(x_18, x_19, x_2, x_3, x_4);
lean_dec(x_2);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
x_22 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printId(x_21, x_2, x_3, x_4);
return x_22;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabPrint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabPrint(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("print");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrint___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
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
static lean_object* _init_l_Lean_Elab_Command_CollectAxioms_State_axioms___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_CollectAxioms_collect_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_1(x_2, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_apply_1(x_3, x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_apply_1(x_4, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_apply_1(x_5, x_20);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_apply_1(x_6, x_22);
return x_23;
}
case 5:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_apply_1(x_9, x_24);
return x_25;
}
case 6:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_apply_1(x_7, x_26);
return x_27;
}
default: 
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_apply_1(x_8, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_CollectAxioms_collect_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CollectAxioms_collect_match__1___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_CollectAxioms_collect_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_CollectAxioms_collect_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_CollectAxioms_collect_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_3);
x_10 = l_Lean_Elab_Command_CollectAxioms_collect(x_9, x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_CollectAxioms_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
case 4:
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
case 5:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_getUsedConstants(x_21);
x_23 = lean_ctor_get(x_19, 4);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_25 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_22, x_24, x_2, x_3);
lean_dec(x_22);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_List_forM___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_23, x_2, x_26);
return x_27;
}
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Expr_getUsedConstants(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_31, x_32, x_2, x_3);
lean_dec(x_31);
return x_33;
}
case 7:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Expr_getUsedConstants(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_37, x_38, x_2, x_3);
lean_dec(x_37);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
lean_dec(x_14);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Expr_getUsedConstants(x_42);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lean_Expr_getUsedConstants(x_44);
x_46 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_47 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_43, x_46, x_2, x_3);
lean_dec(x_43);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_45, x_46, x_2, x_48);
lean_dec(x_45);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
x_50 = lean_box(0);
lean_inc(x_1);
x_51 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_1, x_50);
lean_inc(x_5);
lean_inc(x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_5);
lean_inc(x_1);
lean_inc(x_2);
x_53 = lean_environment_find(x_2, x_1);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
switch (lean_obj_tag(x_55)) {
case 0:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_2);
x_56 = lean_array_push(x_5, x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
case 4:
{
lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
case 5:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_1);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 2);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Expr_getUsedConstants(x_62);
x_64 = lean_ctor_get(x_60, 4);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_66 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_63, x_65, x_2, x_52);
lean_dec(x_63);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_List_forM___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__2(x_64, x_2, x_67);
return x_68;
}
case 6:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_1);
x_69 = lean_ctor_get(x_55, 0);
lean_inc(x_69);
lean_dec(x_55);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get(x_70, 2);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Expr_getUsedConstants(x_71);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_72, x_73, x_2, x_52);
lean_dec(x_72);
return x_74;
}
case 7:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_1);
x_75 = lean_ctor_get(x_55, 0);
lean_inc(x_75);
lean_dec(x_55);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_76, 2);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Expr_getUsedConstants(x_77);
x_79 = lean_unsigned_to_nat(0u);
x_80 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_78, x_79, x_2, x_52);
lean_dec(x_78);
return x_80;
}
default: 
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_1);
x_81 = lean_ctor_get(x_55, 0);
lean_inc(x_81);
lean_dec(x_55);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 2);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Expr_getUsedConstants(x_83);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = l_Lean_Expr_getUsedConstants(x_85);
x_87 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_88 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_84, x_87, x_2, x_52);
lean_dec(x_84);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_86, x_87, x_2, x_89);
lean_dec(x_86);
return x_90;
}
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_3);
return x_92;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_Elab_Command_CollectAxioms_collect___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Array_empty___closed__1;
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
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Array_toList___rarg(x_12);
lean_dec(x_12);
x_20 = l_List_map___main___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___spec__1(x_19);
x_21 = l_Lean_MessageData_ofList(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = 0;
x_26 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_24, x_25, x_2, x_3, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_12);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_1);
x_28 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___closed__5;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = 0;
x_33 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_31, x_32, x_2, x_3, x_7);
return x_33;
}
}
}
lean_object* l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_0__Lean_Elab_Command_printAxiomsOf(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabPrintAxioms___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
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
lean_object* l_Lean_Elab_Command_elabPrintAxioms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
lean_inc(x_2);
x_8 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Print_0__Lean_Elab_Command_printId___spec__1(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_forM___main___at_Lean_Elab_Command_elabPrintAxioms___spec__1(x_9, x_2, x_3, x_10);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabPrintAxioms___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at_Lean_Elab_Command_elabPrintAxioms___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabPrintAxioms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabPrintAxioms(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("printAxioms");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrintAxioms___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrintAxioms(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrintAxioms___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Print(lean_object* w) {
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
l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__2 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__2);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__3 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__3);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__4 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_lparamsToMessageData___closed__4);
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
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printDefLike___closed__1);
l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1 = _init_l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_0__Lean_Elab_Command_printQuot___rarg___closed__1);
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
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1);
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__2);
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabPrint(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_CollectAxioms_State_visited___default = _init_l_Lean_Elab_Command_CollectAxioms_State_visited___default();
lean_mark_persistent(l_Lean_Elab_Command_CollectAxioms_State_visited___default);
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
