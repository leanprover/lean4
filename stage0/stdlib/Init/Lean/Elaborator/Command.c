// Lean compiler output
// Module: Init.Lean.Elaborator.Command
// Imports: Init.Lean.Elaborator.Alias Init.Lean.Elaborator.Basic Init.Lean.Elaborator.ResolveName Init.Lean.Elaborator.Term
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
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1;
lean_object* l_Lean_Elab_elabEnd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toPreTerm(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_logUnknownDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabResolveName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__1;
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenSimple(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3;
lean_object* l_Lean_Elab_elabEnd___closed__4;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3;
lean_object* l_Lean_Elab_elabUniverse(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_put_str(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main___boxed(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Elab_elabUniverse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabNotation(lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3;
lean_object* l_IO_print___at_Lean_Elab_elabElab___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addOpenDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenRenaming___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabExport___closed__1;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_elabExport___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2;
extern lean_object* l_Sigma_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_elabOpenOnly___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabReserve(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabInitQuot___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabUniverses___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getUniverses___rarg(lean_object*);
lean_object* l_Lean_addAlias(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1;
extern lean_object* l_List_repr___rarg___closed__3;
extern lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
lean_object* l_Lean_Elab_elabPreTerm(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1;
extern lean_object* l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* l_Lean_Elab_elabReserve___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace(lean_object*);
extern lean_object* l_Sigma_HasRepr___rarg___closed__2;
lean_object* l_List_head_x21___at_Lean_Elab_getScope___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabElab(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation(lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_getNamespace___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabReserve___rarg(lean_object*);
uint8_t l_Lean_Name_eqStr(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes___boxed(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenHiding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenOnly(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabMixfix(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabInitQuot(lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3;
lean_object* l_Lean_Syntax_lift(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1;
lean_object* l_Lean_Elab_elabEnd(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpen(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2;
extern lean_object* l_Lean_Parser_Command_elab___elambda__1___rarg___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab(lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
extern lean_object* l_IO_println___rarg___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabVariable___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2;
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l_Lean_Elab_elabNotation___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode___rarg(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2;
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1;
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
extern lean_object* l_String_Iterator_HasRepr___closed__2;
lean_object* l_IO_println___at_Lean_Elab_elabElab___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabTermAux___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_preterm___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_elabOpenHiding(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_init__quot___elambda__1___rarg___closed__2;
lean_object* l_Lean_Syntax_getArgs___rarg(lean_object*);
lean_object* l_Lean_Elab_addUniverse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName(lean_object*);
lean_object* l_Lean_Elab_addUniverse___closed__1;
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logElabException(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3;
extern lean_object* l_Lean_Parser_Command_end___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_notation___elambda__1___closed__2;
lean_object* l_Lean_Elab_addUniverse___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1;
lean_object* l_Lean_Elab_getPosition(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2;
lean_object* l_Lean_Elab_elabNotation___rarg(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabElab___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1;
lean_object* l_Lean_addBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabPreTerm___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabExport(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2;
extern lean_object* l_Lean_Parser_Command_reserve___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1;
lean_object* l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabResolveName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabUniverses(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1;
lean_object* l_Lean_Syntax_getIdAt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__6;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_export___elambda__1___closed__2;
lean_object* l_Lean_Elab_getEnv___rarg(lean_object*);
lean_object* l_Lean_Elab_elabElab___closed__1;
lean_object* l_Lean_Elab_elabExport___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1;
lean_object* l_Lean_Elab_elabElab___closed__2;
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* l_Lean_Elab_elabNamespace___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_runIOUnsafe___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3;
lean_object* l_Lean_Elab_elabInitQuot___boxed(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection(lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1;
lean_object* l_Lean_Elab_elabMixfix___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3;
lean_object* l_List_toString___at_Lean_Elab_elabResolveName___spec__1(lean_object*);
lean_object* l_Lean_Elab_addOpenDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(uint8_t, lean_object*);
lean_object* l_Lean_Elab_elabInitQuot___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSection(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx___main___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Command_resolve__name___elambda__1___rarg___closed__2;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenRenaming(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSection___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabNamespace(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elaborator_Command_4__checkEndHeader(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_elabVariable(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__2;
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3;
extern lean_object* l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
lean_object* l_Lean_Elab_setEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__5;
lean_object* l_Lean_Elab_resolveNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenSimple___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen(lean_object*);
lean_object* l_Lean_Elab_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabMixfix___rarg(lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___main(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_1, x_2, x_5, x_4);
x_8 = l_List_head_x21___at_Lean_Elab_getScope___spec__1(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_8, 3);
x_11 = lean_ctor_get(x_8, 7);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 6);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 5);
lean_dec(x_13);
x_14 = lean_ctor_get(x_8, 4);
lean_dec(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_inc(x_6);
x_19 = lean_name_mk_string(x_18, x_6);
x_20 = lean_box(0);
if (x_2 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_6);
x_21 = l_Lean_Options_empty;
x_22 = l_Lean_LocalContext_Inhabited___closed__2;
x_23 = lean_unsigned_to_nat(1u);
x_24 = 0;
lean_ctor_set(x_8, 7, x_23);
lean_ctor_set(x_8, 6, x_22);
lean_ctor_set(x_8, 5, x_20);
lean_ctor_set(x_8, 4, x_20);
lean_ctor_set(x_8, 2, x_21);
lean_ctor_set(x_8, 1, x_19);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*8, x_24);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_name_mk_string(x_10, x_6);
x_27 = l_Lean_Options_empty;
x_28 = l_Lean_LocalContext_Inhabited___closed__2;
x_29 = lean_unsigned_to_nat(1u);
x_30 = 0;
lean_ctor_set(x_8, 7, x_29);
lean_ctor_set(x_8, 6, x_28);
lean_ctor_set(x_8, 5, x_20);
lean_ctor_set(x_8, 4, x_20);
lean_ctor_set(x_8, 3, x_26);
lean_ctor_set(x_8, 2, x_27);
lean_ctor_set(x_8, 1, x_19);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*8, x_30);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_8, 3);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_box(0);
lean_inc(x_6);
x_34 = lean_name_mk_string(x_33, x_6);
x_35 = lean_box(0);
if (x_2 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_6);
x_36 = l_Lean_Options_empty;
x_37 = l_Lean_LocalContext_Inhabited___closed__2;
x_38 = lean_unsigned_to_nat(1u);
x_39 = 0;
x_40 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_32);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_35);
lean_ctor_set(x_40, 6, x_37);
lean_ctor_set(x_40, 7, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_name_mk_string(x_32, x_6);
x_43 = l_Lean_Options_empty;
x_44 = l_Lean_LocalContext_Inhabited___closed__2;
x_45 = lean_unsigned_to_nat(1u);
x_46 = 0;
x_47 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_43);
lean_ctor_set(x_47, 3, x_42);
lean_ctor_set(x_47, 4, x_35);
lean_ctor_set(x_47, 5, x_35);
lean_ctor_set(x_47, 6, x_44);
lean_ctor_set(x_47, 7, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*8, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
}
default: 
{
lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_box(0);
return x_49;
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_1__addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Lean_Elaborator_Command_1__addScopes(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_elabNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_array_get(x_7, x_6, x_8);
x_10 = l_Lean_Syntax_getId___rarg(x_9);
lean_dec(x_9);
x_11 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_12 = 1;
x_13 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_11, x_12, x_10, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 5, x_13);
x_14 = l_Lean_Elab_getNamespace___rarg(x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_16, 0);
x_20 = l_Lean_registerNamespace(x_19, x_18);
lean_ctor_set(x_16, 0, x_20);
x_21 = lean_box(0);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
x_25 = lean_ctor_get(x_16, 2);
x_26 = lean_ctor_get(x_16, 3);
x_27 = lean_ctor_get(x_16, 4);
x_28 = lean_ctor_get(x_16, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_29 = l_Lean_registerNamespace(x_23, x_22);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 5, x_28);
x_31 = lean_box(0);
lean_ctor_set(x_14, 1, x_30);
lean_ctor_set(x_14, 0, x_31);
return x_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_14, 1);
x_33 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 5);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 lean_ctor_release(x_32, 5);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
x_41 = l_Lean_registerNamespace(x_34, x_33);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 6, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 4, x_38);
lean_ctor_set(x_42, 5, x_39);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get(x_3, 3);
x_49 = lean_ctor_get(x_3, 4);
x_50 = lean_ctor_get(x_3, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
x_51 = lean_ctor_get(x_1, 1);
x_52 = lean_box(0);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_array_get(x_52, x_51, x_53);
x_55 = l_Lean_Syntax_getId___rarg(x_54);
lean_dec(x_54);
x_56 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_57 = 1;
x_58 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_56, x_57, x_55, x_50);
lean_dec(x_50);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_45);
lean_ctor_set(x_59, 1, x_46);
lean_ctor_set(x_59, 2, x_47);
lean_ctor_set(x_59, 3, x_48);
lean_ctor_set(x_59, 4, x_49);
lean_ctor_set(x_59, 5, x_58);
x_60 = l_Lean_Elab_getNamespace___rarg(x_59);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 x_70 = x_61;
} else {
 lean_dec_ref(x_61);
 x_70 = lean_box(0);
}
x_71 = l_Lean_registerNamespace(x_64, x_62);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 6, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_65);
lean_ctor_set(x_72, 2, x_66);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set(x_72, 4, x_68);
lean_ctor_set(x_72, 5, x_69);
x_73 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_63;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
lean_object* l_Lean_Elab_elabNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabNamespace(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabNamespace");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabNamespace___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabSection(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Elab_getNamespace___rarg(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_4, x_10);
x_12 = l_Lean_Syntax_getOptionalIdent___rarg(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_8, 5);
x_15 = lean_box(0);
x_16 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_17 = lean_box(0);
x_18 = l_Lean_Options_empty;
x_19 = l_Lean_LocalContext_Inhabited___closed__2;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_7);
lean_ctor_set(x_21, 4, x_15);
lean_ctor_set(x_21, 5, x_15);
lean_ctor_set(x_21, 6, x_19);
lean_ctor_set(x_21, 7, x_10);
lean_ctor_set_uint8(x_21, sizeof(void*)*8, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_8, 5, x_22);
x_23 = lean_box(0);
lean_ctor_set(x_5, 0, x_23);
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 4);
x_29 = lean_ctor_get(x_8, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_30 = lean_box(0);
x_31 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_32 = lean_box(0);
x_33 = l_Lean_Options_empty;
x_34 = l_Lean_LocalContext_Inhabited___closed__2;
x_35 = 0;
x_36 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_7);
lean_ctor_set(x_36, 4, x_30);
lean_ctor_set(x_36, 5, x_30);
lean_ctor_set(x_36, 6, x_34);
lean_ctor_set(x_36, 7, x_10);
lean_ctor_set_uint8(x_36, sizeof(void*)*8, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_26);
lean_ctor_set(x_38, 3, x_27);
lean_ctor_set(x_38, 4, x_28);
lean_ctor_set(x_38, 5, x_37);
x_39 = lean_box(0);
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_7);
x_40 = lean_ctor_get(x_12, 0);
lean_inc(x_40);
lean_dec(x_12);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_8, 5);
x_43 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_44 = 0;
x_45 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_43, x_44, x_40, x_42);
lean_dec(x_42);
lean_ctor_set(x_8, 5, x_45);
x_46 = lean_box(0);
lean_ctor_set(x_5, 0, x_46);
return x_5;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_8, 0);
x_48 = lean_ctor_get(x_8, 1);
x_49 = lean_ctor_get(x_8, 2);
x_50 = lean_ctor_get(x_8, 3);
x_51 = lean_ctor_get(x_8, 4);
x_52 = lean_ctor_get(x_8, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_8);
x_53 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_54 = 0;
x_55 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_53, x_54, x_40, x_52);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_50);
lean_ctor_set(x_56, 4, x_51);
lean_ctor_set(x_56, 5, x_55);
x_57 = lean_box(0);
lean_ctor_set(x_5, 1, x_56);
lean_ctor_set(x_5, 0, x_57);
return x_5;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_5, 0);
x_59 = lean_ctor_get(x_5, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_5);
x_60 = lean_box(0);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_array_get(x_60, x_4, x_61);
x_63 = l_Lean_Syntax_getOptionalIdent___rarg(x_62);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_59, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_59, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
x_72 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_73 = lean_box(0);
x_74 = l_Lean_Options_empty;
x_75 = l_Lean_LocalContext_Inhabited___closed__2;
x_76 = 0;
x_77 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_58);
lean_ctor_set(x_77, 4, x_71);
lean_ctor_set(x_77, 5, x_71);
lean_ctor_set(x_77, 6, x_75);
lean_ctor_set(x_77, 7, x_61);
lean_ctor_set_uint8(x_77, sizeof(void*)*8, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_69);
if (lean_is_scalar(x_70)) {
 x_79 = lean_alloc_ctor(0, 6, 0);
} else {
 x_79 = x_70;
}
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_65);
lean_ctor_set(x_79, 2, x_66);
lean_ctor_set(x_79, 3, x_67);
lean_ctor_set(x_79, 4, x_68);
lean_ctor_set(x_79, 5, x_78);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_58);
x_82 = lean_ctor_get(x_63, 0);
lean_inc(x_82);
lean_dec(x_63);
x_83 = lean_ctor_get(x_59, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_59, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_59, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_59, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_59, 4);
lean_inc(x_87);
x_88 = lean_ctor_get(x_59, 5);
lean_inc(x_88);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 x_89 = x_59;
} else {
 lean_dec_ref(x_59);
 x_89 = lean_box(0);
}
x_90 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_91 = 0;
x_92 = l___private_Init_Lean_Elaborator_Command_1__addScopes___main(x_90, x_91, x_82, x_88);
lean_dec(x_88);
if (lean_is_scalar(x_89)) {
 x_93 = lean_alloc_ctor(0, 6, 0);
} else {
 x_93 = x_89;
}
lean_ctor_set(x_93, 0, x_83);
lean_ctor_set(x_93, 1, x_84);
lean_ctor_set(x_93, 2, x_85);
lean_ctor_set(x_93, 3, x_86);
lean_ctor_set(x_93, 4, x_87);
lean_ctor_set(x_93, 5, x_92);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
lean_object* l_Lean_Elab_elabSection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabSection(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSection");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabSection___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_getNumParts___main(x_3);
return x_4;
}
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lean_Name_eqStr(x_9, x_7);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_6;
x_2 = x_8;
goto _start;
}
}
}
default: 
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Elaborator_Command_4__checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', insufficient scopes");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabEnd___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name is missing");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabEnd___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name mismatch");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabEnd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabEnd___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_List_lengthAux___main___rarg(x_5, x_7);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_6, x_10);
x_12 = l_Lean_Syntax_getOptionalIdent___rarg(x_11);
lean_dec(x_11);
x_13 = l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(x_12);
x_14 = lean_nat_dec_lt(x_13, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_nat_sub(x_8, x_10);
lean_dec(x_8);
x_16 = l_List_drop___main___rarg(x_15, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 5, x_16);
x_17 = l_Lean_Elab_elabEnd___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_8);
x_19 = l_List_drop___main___rarg(x_13, x_5);
lean_ctor_set(x_3, 5, x_19);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_20; 
x_20 = l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(x_5);
lean_dec(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_elabEnd___closed__4;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(x_25, x_5);
lean_dec(x_5);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Elab_elabEnd___closed__6;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_ctor_get(x_3, 2);
x_34 = lean_ctor_get(x_3, 3);
x_35 = lean_ctor_get(x_3, 4);
x_36 = lean_ctor_get(x_3, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_3);
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_List_lengthAux___main___rarg(x_36, x_38);
x_40 = lean_box(0);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_array_get(x_40, x_37, x_41);
x_43 = l_Lean_Syntax_getOptionalIdent___rarg(x_42);
lean_dec(x_42);
x_44 = l___private_Init_Lean_Elaborator_Command_2__getNumEndScopes(x_43);
x_45 = lean_nat_dec_lt(x_44, x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_44);
lean_dec(x_43);
x_46 = lean_nat_sub(x_39, x_41);
lean_dec(x_39);
x_47 = l_List_drop___main___rarg(x_46, x_36);
lean_dec(x_36);
x_48 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_48, 0, x_31);
lean_ctor_set(x_48, 1, x_32);
lean_ctor_set(x_48, 2, x_33);
lean_ctor_set(x_48, 3, x_34);
lean_ctor_set(x_48, 4, x_35);
lean_ctor_set(x_48, 5, x_47);
x_49 = l_Lean_Elab_elabEnd___closed__2;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_39);
x_51 = l_List_drop___main___rarg(x_44, x_36);
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_31);
lean_ctor_set(x_52, 1, x_32);
lean_ctor_set(x_52, 2, x_33);
lean_ctor_set(x_52, 3, x_34);
lean_ctor_set(x_52, 4, x_35);
lean_ctor_set(x_52, 5, x_51);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_53; 
x_53 = l___private_Init_Lean_Elaborator_Command_3__checkAnonymousScope(x_36);
lean_dec(x_36);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_Elab_elabEnd___closed__4;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
return x_57;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_43, 0);
lean_inc(x_58);
lean_dec(x_43);
x_59 = l___private_Init_Lean_Elaborator_Command_4__checkEndHeader___main(x_58, x_36);
lean_dec(x_36);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Elab_elabEnd___closed__6;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_52);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_52);
return x_63;
}
}
}
}
}
}
lean_object* l_Lean_Elab_elabEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabEnd(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabEnd");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabEnd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_end___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_elabExport___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_array_fget(x_5, x_6);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_16 = l_Lean_Syntax_getId___rarg(x_13);
lean_inc(x_16);
x_17 = l_Lean_Name_append___main(x_2, x_16);
x_18 = l_Lean_Environment_contains(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = l_Lean_Elab_logUnknownDecl___rarg(x_13, x_17, x_8, x_9);
lean_dec(x_13);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_6 = x_15;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
x_22 = l_Lean_Name_append___main(x_3, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
x_6 = x_15;
x_7 = x_24;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_addAlias(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
lean_object* _init_l_Lean_Elab_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'export', self export");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabExport___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabExport(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_getNamespace___rarg(x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_name_eq(x_10, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_12);
x_17 = l_Lean_Elab_getEnv___rarg(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_array_get(x_5, x_4, x_21);
x_23 = l_Lean_Syntax_getArgs___rarg(x_22);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_iterateMAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_10, x_14, x_18, x_23, x_24, x_20, x_2, x_19);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_10);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_27, 0);
x_31 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_30, x_29);
lean_ctor_set(x_27, 0, x_31);
x_32 = lean_box(0);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
x_36 = lean_ctor_get(x_27, 2);
x_37 = lean_ctor_get(x_27, 3);
x_38 = lean_ctor_get(x_27, 4);
x_39 = lean_ctor_get(x_27, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_40 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_34, x_33);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_39);
x_42 = lean_box(0);
lean_ctor_set(x_25, 1, x_41);
lean_ctor_set(x_25, 0, x_42);
return x_25;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_25, 1);
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
lean_inc(x_44);
lean_dec(x_25);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 5);
lean_inc(x_50);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 x_51 = x_43;
} else {
 lean_dec_ref(x_43);
 x_51 = lean_box(0);
}
x_52 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_45, x_44);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 6, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set(x_53, 2, x_47);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_49);
lean_ctor_set(x_53, 5, x_50);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; 
lean_dec(x_14);
lean_dec(x_10);
x_56 = l_Lean_Elab_elabExport___closed__2;
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_56);
return x_12;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_12, 0);
x_58 = lean_ctor_get(x_12, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_12);
x_59 = lean_name_eq(x_10, x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_60 = l_Lean_Elab_getEnv___rarg(x_58);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_box(0);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_array_get(x_5, x_4, x_64);
x_66 = l_Lean_Syntax_getArgs___rarg(x_65);
lean_dec(x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Array_iterateMAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_10, x_57, x_61, x_66, x_67, x_63, x_2, x_62);
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_57);
lean_dec(x_10);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_69, 5);
lean_inc(x_77);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 lean_ctor_release(x_69, 4);
 lean_ctor_release(x_69, 5);
 x_78 = x_69;
} else {
 lean_dec_ref(x_69);
 x_78 = lean_box(0);
}
x_79 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_72, x_70);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 6, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_73);
lean_ctor_set(x_80, 2, x_74);
lean_ctor_set(x_80, 3, x_75);
lean_ctor_set(x_80, 4, x_76);
lean_ctor_set(x_80, 5, x_77);
x_81 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_71;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_57);
lean_dec(x_10);
x_83 = l_Lean_Elab_elabExport___closed__2;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_58);
return x_84;
}
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_9);
if (x_85 == 0)
{
return x_9;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_9, 0);
x_87 = lean_ctor_get(x_9, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_9);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_elabExport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at_Lean_Elab_elabExport___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_elabExport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabExport(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabExport");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabExport___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_export___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 5);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 5);
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 4, x_13);
lean_ctor_set(x_14, 5, x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_3, 5);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 4);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_17, 4, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_3, 5, x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
x_30 = lean_ctor_get(x_17, 2);
x_31 = lean_ctor_get(x_17, 3);
x_32 = lean_ctor_get(x_17, 4);
x_33 = lean_ctor_get(x_17, 5);
x_34 = lean_ctor_get(x_17, 6);
x_35 = lean_ctor_get(x_17, 7);
x_36 = lean_ctor_get_uint8(x_17, sizeof(void*)*8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_1);
x_37 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_4);
lean_ctor_set(x_37, 5, x_33);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_21);
lean_ctor_set(x_3, 5, x_38);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_17, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_17, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_17, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_17, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_17, 6);
lean_inc(x_48);
x_49 = lean_ctor_get(x_17, 7);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_17, sizeof(void*)*8);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 x_51 = x_17;
} else {
 lean_dec_ref(x_17);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_46);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 8, 1);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set(x_53, 3, x_45);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_47);
lean_ctor_set(x_53, 6, x_48);
lean_ctor_set(x_53, 7, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*8, x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
lean_ctor_set(x_3, 5, x_54);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_3, 1);
x_59 = lean_ctor_get(x_3, 2);
x_60 = lean_ctor_get(x_3, 3);
x_61 = lean_ctor_get(x_3, 4);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_3);
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_63 = x_4;
} else {
 lean_dec_ref(x_4);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_17, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_17, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_17, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_17, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_17, 5);
lean_inc(x_69);
x_70 = lean_ctor_get(x_17, 6);
lean_inc(x_70);
x_71 = lean_ctor_get(x_17, 7);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_17, sizeof(void*)*8);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 x_73 = x_17;
} else {
 lean_dec_ref(x_17);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_63;
}
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_68);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 8, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_65);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_74);
lean_ctor_set(x_75, 5, x_69);
lean_ctor_set(x_75, 6, x_70);
lean_ctor_set(x_75, 7, x_71);
lean_ctor_set_uint8(x_75, sizeof(void*)*8, x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_62);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_57);
lean_ctor_set(x_77, 1, x_58);
lean_ctor_set(x_77, 2, x_59);
lean_ctor_set(x_77, 3, x_60);
lean_ctor_set(x_77, 4, x_61);
lean_ctor_set(x_77, 5, x_76);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
lean_object* l_Lean_Elab_addOpenDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_addOpenDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_addOpenDecl(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
x_11 = l_Lean_Syntax_getId___rarg(x_10);
lean_dec(x_10);
x_12 = l_Lean_Elab_resolveNamespace(x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_16, x_5, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_20;
x_4 = x_18;
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
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
lean_object* l_Lean_Elab_elabOpenSimple(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs___rarg(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_box(0);
x_11 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(x_9, x_8, x_6, x_10, x_2, x_3);
lean_dec(x_8);
return x_11;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_elabOpenSimple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpenSimple(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
x_11 = lean_array_fget(x_3, x_4);
x_12 = l_Lean_Syntax_getId___rarg(x_11);
lean_inc(x_12);
x_13 = l_Lean_Name_append___main(x_1, x_12);
x_14 = l_Lean_Elab_getEnv___rarg(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Environment_contains(x_15, x_13);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_18 = l_Lean_Elab_logUnknownDecl___rarg(x_11, x_13, x_6, x_16);
lean_dec(x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_21;
x_5 = x_19;
x_7 = x_20;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_13);
x_24 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_23, x_6, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_27;
x_5 = x_25;
x_7 = x_26;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_elabOpenOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_array_get(x_5, x_4, x_12);
x_14 = l_Lean_Syntax_getArgs___rarg(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_box(0);
x_17 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_10, x_15, x_14, x_6, x_16, x_2, x_11);
lean_dec(x_14);
lean_dec(x_10);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_elabOpenOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpenOnly(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = l_Lean_Syntax_getId___rarg(x_12);
lean_inc(x_13);
x_14 = l_Lean_Name_append___main(x_1, x_13);
x_15 = l_Lean_Environment_contains(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_16 = l_Lean_Elab_logUnknownDecl___rarg(x_12, x_14, x_7, x_8);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_18;
x_8 = x_17;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_6);
x_21 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_21;
x_6 = x_20;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_elabOpenHiding(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_getEnv___rarg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_array_get(x_5, x_4, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Syntax_getArgs___rarg(x_16);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_10, x_13, x_19, x_18, x_6, x_17, x_2, x_14);
lean_dec(x_18);
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_23, x_2, x_22);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_elabOpenHiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpenHiding(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_5);
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getIdAt___rarg(x_11, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getIdAt___rarg(x_11, x_14);
x_16 = l_Lean_Name_append___main(x_1, x_13);
x_17 = l_Lean_Elab_getEnv___rarg(x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Environment_contains(x_18, x_16);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
x_21 = l_Lean_Elab_logUnknownDecl___rarg(x_11, x_16, x_6, x_19);
lean_dec(x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_24;
x_5 = x_22;
x_7 = x_23;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_16);
x_27 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_26, x_6, x_19);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_30;
x_5 = x_28;
x_7 = x_29;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_elabOpenRenaming(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_array_get(x_5, x_4, x_12);
x_14 = l_Lean_Syntax_getArgs___rarg(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_10, x_12, x_14, x_6, x_15, x_2, x_11);
lean_dec(x_14);
lean_dec(x_10);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_elabOpenRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpenRenaming(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_elabOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_asNode___rarg(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
x_11 = lean_name_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
x_13 = lean_name_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
x_15 = lean_name_eq(x_9, x_14);
lean_dec(x_9);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Elab_elabOpenRenaming(x_8, x_2, x_3);
lean_dec(x_8);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Elab_elabOpenHiding(x_8, x_2, x_3);
lean_dec(x_8);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = l_Lean_Elab_elabOpenOnly(x_8, x_2, x_3);
lean_dec(x_8);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_9);
x_19 = l_Lean_Elab_elabOpenSimple(x_8, x_2, x_3);
lean_dec(x_8);
return x_19;
}
}
}
lean_object* l_Lean_Elab_elabOpen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabOpen(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabOpen");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabOpen___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_open___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 5);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 5);
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 4, x_13);
lean_ctor_set(x_14, 5, x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_3, 5);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 5);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_17, 5, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_3, 5, x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
x_30 = lean_ctor_get(x_17, 2);
x_31 = lean_ctor_get(x_17, 3);
x_32 = lean_ctor_get(x_17, 4);
x_33 = lean_ctor_get(x_17, 5);
x_34 = lean_ctor_get(x_17, 6);
x_35 = lean_ctor_get(x_17, 7);
x_36 = lean_ctor_get_uint8(x_17, sizeof(void*)*8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_1);
x_37 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_37, 5, x_4);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_21);
lean_ctor_set(x_3, 5, x_38);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_3);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_17, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_17, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_17, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_17, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_17, 6);
lean_inc(x_48);
x_49 = lean_ctor_get(x_17, 7);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_17, sizeof(void*)*8);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 x_51 = x_17;
} else {
 lean_dec_ref(x_17);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_47);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 8, 1);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set(x_53, 3, x_45);
lean_ctor_set(x_53, 4, x_46);
lean_ctor_set(x_53, 5, x_52);
lean_ctor_set(x_53, 6, x_48);
lean_ctor_set(x_53, 7, x_49);
lean_ctor_set_uint8(x_53, sizeof(void*)*8, x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
lean_ctor_set(x_3, 5, x_54);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_3, 1);
x_59 = lean_ctor_get(x_3, 2);
x_60 = lean_ctor_get(x_3, 3);
x_61 = lean_ctor_get(x_3, 4);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_3);
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_63 = x_4;
} else {
 lean_dec_ref(x_4);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_17, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_17, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_17, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_17, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_17, 5);
lean_inc(x_69);
x_70 = lean_ctor_get(x_17, 6);
lean_inc(x_70);
x_71 = lean_ctor_get(x_17, 7);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_17, sizeof(void*)*8);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 x_73 = x_17;
} else {
 lean_dec_ref(x_17);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_63;
}
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_69);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 8, 1);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_65);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_68);
lean_ctor_set(x_75, 5, x_74);
lean_ctor_set(x_75, 6, x_70);
lean_ctor_set(x_75, 7, x_71);
lean_ctor_set_uint8(x_75, sizeof(void*)*8, x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_62);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_57);
lean_ctor_set(x_77, 1, x_58);
lean_ctor_set(x_77, 2, x_59);
lean_ctor_set(x_77, 3, x_60);
lean_ctor_set(x_77, 4, x_61);
lean_ctor_set(x_77, 5, x_76);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
lean_object* _init_l_Lean_Elab_addUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a universe named '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_addUniverse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been declared in this Scope");
return x_1;
}
}
lean_object* l_Lean_Elab_addUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Syntax_getId___rarg(x_1);
x_5 = l_Lean_Elab_getUniverses___rarg(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_4, x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_4, x_2, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_4);
x_12 = l_Lean_Elab_addUniverse___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_Elab_addUniverse___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_Elab_logError___rarg(x_1, x_15, x_2, x_7);
return x_16;
}
}
}
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_addUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_addUniverse(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_elabUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Elab_addUniverse(x_7, x_2, x_3);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_elabUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabUniverse(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabUniverse");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabUniverse___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_universe___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
x_11 = l_Lean_Elab_addUniverse(x_10, x_5, x_6);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
x_6 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_Elab_elabUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs___rarg(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_box(0);
x_11 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(x_6, x_8, x_9, x_10, x_2, x_3);
lean_dec(x_8);
return x_11;
}
}
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_elabUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabUniverses(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabUniverses");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabUniverses___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_universes___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabInitQuot___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Elab_getEnv___rarg(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(4);
x_7 = lean_add_decl(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Elab_logElabException(x_9, x_1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Elab_setEnv(x_11, x_1, x_5);
return x_12;
}
}
}
lean_object* l_Lean_Elab_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabInitQuot___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabInitQuot___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_elabInitQuot___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_elabInitQuot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_elabInitQuot(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabInitQuot");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabInitQuot___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_init__quot___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_runIOUnsafe___rarg(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_elabVariable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabVariable(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabVariable");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabVariable___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_variable___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_1, x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Nat_repr(x_7);
x_10 = l_Prod_HasRepr___rarg___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_8);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = l_Option_HasRepr___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_12, x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_19, x_6);
lean_dec(x_6);
return x_20;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_21; 
x_21 = l_String_splitAux___main___closed__1;
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = 0;
x_25 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_24, x_23);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Nat_repr(x_26);
x_29 = l_Prod_HasRepr___rarg___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_List_reprAux___main___rarg___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_27);
x_35 = lean_string_append(x_32, x_34);
lean_dec(x_34);
x_36 = l_Option_HasRepr___rarg___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_25);
lean_dec(x_25);
return x_38;
}
}
}
}
lean_object* l_List_toString___at_Lean_Elab_elabResolveName___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_elabResolveName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveName(x_8, x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_getPosition(x_12, x_2, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_10);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Nat_repr(x_17);
x_20 = l_Sigma_HasRepr___rarg___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_List_reprAux___main___rarg___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_repr(x_18);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = l_Sigma_HasRepr___rarg___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_String_Iterator_HasRepr___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_16);
lean_dec(x_16);
x_31 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = l_Lean_Elab_runIOUnsafe___rarg(x_31, x_2, x_15);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_elabResolveName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabResolveName(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabResolveName");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabResolveName___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_resolve__name___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabPreTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_IO_println___at___private_Init_Lean_Parser_Module_4__testModuleParserAux___main___spec__1), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_runIOUnsafe___rarg(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = x_7;
lean_inc(x_2);
x_12 = l_Lean_Elab_toPreTerm(x_11, x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_expr_dbg_to_string(x_13);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_runIOUnsafe___rarg(x_16, x_2, x_14);
lean_dec(x_2);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
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
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
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
lean_dec(x_7);
lean_dec(x_2);
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
lean_object* l_Lean_Elab_elabPreTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabPreTerm(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabPreTerm");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabPreTerm___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_preterm___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_IO_print___at_Lean_Elab_elabElab___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Syntax_formatStx___main___rarg(x_1);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
x_6 = lean_io_prim_put_str(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_IO_println___at_Lean_Elab_elabElab___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at_Lean_Elab_elabElab___spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_IO_println___rarg___closed__1;
x_6 = lean_io_prim_put_str(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* _init_l_Lean_Elab_elabElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to elaborate syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_elabElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabElab___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabElab(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get(x_6, x_4, x_7);
x_9 = x_8;
x_10 = 0;
lean_inc(x_2);
x_11 = l_Lean_Elab_elabTermAux___main(x_9, x_5, x_10, x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_expr_dbg_to_string(x_28);
lean_dec(x_28);
x_30 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Lean_Elab_runIOUnsafe___rarg(x_30, x_2, x_13);
lean_dec(x_2);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_box(0);
x_14 = x_32;
goto block_27;
}
block_27:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l_IO_println___at_Lean_Elab_elabElab___spec__1), 2, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = l_Lean_Elab_runIOUnsafe___rarg(x_15, x_2, x_13);
lean_dec(x_2);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = l_Lean_Elab_elabElab___closed__2;
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_Elab_elabElab___closed__2;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Elab_elabElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_elabElab(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabElab");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabElab___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_elab___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabMixfix___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_elabMixfix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_elabMixfix___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_elabMixfix___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_elabMixfix(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabMixfix");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabMixfix___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabReserve___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_elabReserve(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_elabReserve___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_elabReserve___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_elabReserve(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabReserve");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabReserve___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_reserve___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabNotation___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_elabNotation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_elabNotation___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_elabNotation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_elabNotation(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabNotation");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_elabNotation___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_notation___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Elaborator_Alias(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_Basic(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_ResolveName(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elaborator_Command(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elaborator_Alias(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elaborator_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elaborator_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elaborator_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabNamespace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabSection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_elabEnd___closed__1 = _init_l_Lean_Elab_elabEnd___closed__1();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__1);
l_Lean_Elab_elabEnd___closed__2 = _init_l_Lean_Elab_elabEnd___closed__2();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__2);
l_Lean_Elab_elabEnd___closed__3 = _init_l_Lean_Elab_elabEnd___closed__3();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__3);
l_Lean_Elab_elabEnd___closed__4 = _init_l_Lean_Elab_elabEnd___closed__4();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__4);
l_Lean_Elab_elabEnd___closed__5 = _init_l_Lean_Elab_elabEnd___closed__5();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__5);
l_Lean_Elab_elabEnd___closed__6 = _init_l_Lean_Elab_elabEnd___closed__6();
lean_mark_persistent(l_Lean_Elab_elabEnd___closed__6);
l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabEnd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_elabExport___closed__1 = _init_l_Lean_Elab_elabExport___closed__1();
lean_mark_persistent(l_Lean_Elab_elabExport___closed__1);
l_Lean_Elab_elabExport___closed__2 = _init_l_Lean_Elab_elabExport___closed__2();
lean_mark_persistent(l_Lean_Elab_elabExport___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabExport(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabOpen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_addUniverse___closed__1 = _init_l_Lean_Elab_addUniverse___closed__1();
lean_mark_persistent(l_Lean_Elab_addUniverse___closed__1);
l_Lean_Elab_addUniverse___closed__2 = _init_l_Lean_Elab_addUniverse___closed__2();
lean_mark_persistent(l_Lean_Elab_addUniverse___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabUniverse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabUniverses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabInitQuot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabVariable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabPreTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_elabElab___closed__1 = _init_l_Lean_Elab_elabElab___closed__1();
lean_mark_persistent(l_Lean_Elab_elabElab___closed__1);
l_Lean_Elab_elabElab___closed__2 = _init_l_Lean_Elab_elabElab___closed__2();
lean_mark_persistent(l_Lean_Elab_elabElab___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabElab(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabMixfix(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabReserve(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_elabNotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
