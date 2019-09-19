// Lean compiler output
// Module: init.lean.elaborator.command
// Imports: init.lean.elaborator.alias init.lean.elaborator.basic init.lean.elaborator.resolvename init.lean.elaborator.term
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
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3;
lean_object* l_Lean_Elab_elabNotation___rarg(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection(lean_object*);
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_command_4__checkEndHeader___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addOpenDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenSimple(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSection(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_command_1__addScopes___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3;
lean_object* l_Lean_Elab_elabInitQuot___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Sigma_HasRepr___rarg___closed__1;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runIOUnsafe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2;
lean_object* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l_Lean_Elab_elabEnd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpen(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2;
extern lean_object* l_Lean_Parser_Command_export___elambda__1___closed__2;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1;
lean_object* l_Lean_Elab_elabEnd___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2;
lean_object* lean_add_decl(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot(lean_object*);
lean_object* l_Lean_Syntax_formatStx___main___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix(lean_object*);
lean_object* l_Lean_Elab_elabExport___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2;
lean_object* l_Lean_Elab_addUniverse___closed__2;
extern lean_object* l_Lean_Parser_Command_elab___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSection___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenHiding(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(uint8_t, lean_object*);
lean_object* l_Lean_Elab_elabResolveName(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_asNode___rarg(lean_object*);
lean_object* l_Lean_Elab_elabInitQuot(lean_object*);
lean_object* l_List_head___at_Lean_Elab_getScope___spec__1(lean_object*);
lean_object* l_Lean_Elab_elabElab(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1;
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_init_lean_elaborator_command_3__checkAnonymousScope(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse(lean_object*);
lean_object* lean_io_prim_put_str(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3;
extern lean_object* l_Lean_Parser_Command_preterm___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_addUniverse___closed__1;
lean_object* l_Lean_Elab_elabOpenOnly___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabVariable(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Elab_addOpenDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabMixfix___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses(lean_object*);
lean_object* l_Lean_Elab_elabUniverses(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation(lean_object*);
lean_object* l___private_init_lean_elaborator_command_1__addScopes(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1;
lean_object* l_Lean_Elab_elabNamespace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(lean_object*, lean_object*);
lean_object* l___private_init_lean_elaborator_command_3__checkAnonymousScope___boxed(lean_object*);
lean_object* l_Lean_Elab_resolveNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabMixfix___rarg(lean_object*);
lean_object* l_Lean_Syntax_lift(lean_object*, lean_object*);
lean_object* l_Lean_Elab_setEnv(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_Elab_getNamespace___rarg(lean_object*);
lean_object* l_Lean_Elab_elabOpenRenaming(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
lean_object* l_Lean_addAlias(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* l___private_init_lean_elaborator_command_1__addScopes___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabVariable___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1;
uint8_t l___private_init_lean_elaborator_command_4__checkEndHeader___main(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve(lean_object*);
lean_object* l_Lean_Elab_elabElab___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabExport___closed__1;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_Elab_addUniverse___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabElab___closed__2;
lean_object* l_Lean_Elab_elabExport___closed__2;
lean_object* l_Lean_Syntax_getArgs___rarg(lean_object*);
lean_object* l_IO_println___at_Lean_Elab_elabElab___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__2;
lean_object* l_Lean_Syntax_getId___rarg(lean_object*);
lean_object* l_Lean_Elab_elabExport(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_resolve__name___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_notation___elambda__1___closed__2;
lean_object* l___private_init_lean_elaborator_command_1__addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getUniverses___rarg(lean_object*);
lean_object* l_Array_fget(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_String_Iterator_HasRepr___closed__2;
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
lean_object* l_Lean_Elab_elabOpen___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_elabNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_print___at_Lean_Elab_elabElab___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenSimple___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3;
lean_object* l_Lean_Elab_elabNotation___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3;
lean_object* l_Lean_Elab_elabEnd___closed__6;
uint8_t l_Lean_Name_eqStr(lean_object*, lean_object*);
lean_object* l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabVariable(lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabUniverses___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabPreTerm___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Sigma_HasRepr___rarg___closed__2;
lean_object* l_Lean_Elab_elabTermAux___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabInitQuot___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2;
lean_object* l_Lean_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabReserve___rarg(lean_object*);
lean_object* l___private_init_lean_elaborator_command_2__getNumEndScopes___boxed(lean_object*);
lean_object* l___private_init_lean_elaborator_command_2__getNumEndScopes(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabUniverse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1;
lean_object* l_List_toString___at_Lean_Elab_elabResolveName___spec__1(lean_object*);
lean_object* l_Lean_Elab_elabEnd(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_toPreTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__5;
lean_object* l_Lean_Elab_getEnv___rarg(lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___rarg___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2;
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabElab___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabExport(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace(lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3;
lean_object* l_Lean_Elab_getPosition(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_init_lean_elaborator_command_4__checkEndHeader___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabEnd___closed__3;
extern lean_object* l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
lean_object* l_Lean_Elab_elabResolveName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenOnly(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_init__quot___elambda__1___rarg___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3;
lean_object* l_Lean_Elab_elabEnd___closed__1;
lean_object* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_reserve___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1;
lean_object* l_Lean_Elab_logElabException(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabInitQuot___boxed(lean_object*);
lean_object* l_Lean_Elab_elabMixfix(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1;
uint8_t l___private_init_lean_elaborator_command_4__checkEndHeader(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabOpenHiding___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabPreTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabNotation(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabPreTerm(lean_object*);
lean_object* l_Lean_Elab_elabReserve(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptionalIdent___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Command_end___elambda__1___rarg___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_println___rarg___closed__1;
lean_object* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3;
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___rarg___closed__2;
extern lean_object* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
lean_object* l_Lean_Elab_elabUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Elab_elabOpenRenaming___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabReserve___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_init_lean_elaborator_command_1__addScopes___main(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
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
x_7 = l___private_init_lean_elaborator_command_1__addScopes___main(x_1, x_2, x_5, x_4);
x_8 = l_List_head___at_Lean_Elab_getScope___spec__1(x_7);
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
x_22 = l_Lean_LocalContext_Inhabited___closed__1;
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
x_28 = l_Lean_LocalContext_Inhabited___closed__1;
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
x_37 = l_Lean_LocalContext_Inhabited___closed__1;
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
x_44 = l_Lean_LocalContext_Inhabited___closed__1;
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
lean_object* l___private_init_lean_elaborator_command_1__addScopes___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_init_lean_elaborator_command_1__addScopes___main(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l___private_init_lean_elaborator_command_1__addScopes(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_init_lean_elaborator_command_1__addScopes___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_init_lean_elaborator_command_1__addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_init_lean_elaborator_command_1__addScopes(x_1, x_5, x_3, x_4);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_array_get(x_8, x_5, x_9);
x_11 = l_Lean_Syntax_getId___rarg(x_10);
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_6, 5);
x_14 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_15 = 1;
x_16 = l___private_init_lean_elaborator_command_1__addScopes___main(x_14, x_15, x_11, x_13);
lean_dec(x_13);
lean_ctor_set(x_6, 5, x_16);
x_17 = lean_box(0);
lean_ctor_set(x_3, 0, x_17);
x_18 = l_Lean_Elab_getNamespace___rarg(x_3);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_20, 0);
x_24 = l_Lean_registerNamespace(x_23, x_22);
lean_ctor_set(x_20, 0, x_24);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 2);
x_29 = lean_ctor_get(x_20, 3);
x_30 = lean_ctor_get(x_20, 4);
x_31 = lean_ctor_get(x_20, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_32 = l_Lean_registerNamespace(x_26, x_25);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_30);
lean_ctor_set(x_33, 5, x_31);
lean_ctor_set(x_18, 1, x_33);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_18, 1);
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 5);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 lean_ctor_release(x_34, 5);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
x_43 = l_Lean_registerNamespace(x_36, x_35);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 6, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_40);
lean_ctor_set(x_44, 5, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_17);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
return x_18;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_18);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_6, 0);
x_51 = lean_ctor_get(x_6, 1);
x_52 = lean_ctor_get(x_6, 2);
x_53 = lean_ctor_get(x_6, 3);
x_54 = lean_ctor_get(x_6, 4);
x_55 = lean_ctor_get(x_6, 5);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_6);
x_56 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_57 = 1;
x_58 = l___private_init_lean_elaborator_command_1__addScopes___main(x_56, x_57, x_11, x_55);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_52);
lean_ctor_set(x_59, 3, x_53);
lean_ctor_set(x_59, 4, x_54);
lean_ctor_set(x_59, 5, x_58);
x_60 = lean_box(0);
lean_ctor_set(x_3, 1, x_59);
lean_ctor_set(x_3, 0, x_60);
x_61 = l_Lean_Elab_getNamespace___rarg(x_3);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 5);
lean_inc(x_70);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 lean_ctor_release(x_62, 5);
 x_71 = x_62;
} else {
 lean_dec_ref(x_62);
 x_71 = lean_box(0);
}
x_72 = l_Lean_registerNamespace(x_65, x_63);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 6, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
lean_ctor_set(x_73, 2, x_67);
lean_ctor_set(x_73, 3, x_68);
lean_ctor_set(x_73, 4, x_69);
lean_ctor_set(x_73, 5, x_70);
if (lean_is_scalar(x_64)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_64;
}
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_61, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_77 = x_61;
} else {
 lean_dec_ref(x_61);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_79 = lean_ctor_get(x_1, 1);
x_80 = lean_ctor_get(x_3, 1);
lean_inc(x_80);
lean_dec(x_3);
x_81 = lean_box(0);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_array_get(x_81, x_79, x_82);
x_84 = l_Lean_Syntax_getId___rarg(x_83);
lean_dec(x_83);
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_80, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_80, 5);
lean_inc(x_90);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 x_91 = x_80;
} else {
 lean_dec_ref(x_80);
 x_91 = lean_box(0);
}
x_92 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_93 = 1;
x_94 = l___private_init_lean_elaborator_command_1__addScopes___main(x_92, x_93, x_84, x_90);
lean_dec(x_90);
if (lean_is_scalar(x_91)) {
 x_95 = lean_alloc_ctor(0, 6, 0);
} else {
 x_95 = x_91;
}
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_86);
lean_ctor_set(x_95, 2, x_87);
lean_ctor_set(x_95, 3, x_88);
lean_ctor_set(x_95, 4, x_89);
lean_ctor_set(x_95, 5, x_94);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Elab_getNamespace___rarg(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_99, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_99, 5);
lean_inc(x_107);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 lean_ctor_release(x_99, 5);
 x_108 = x_99;
} else {
 lean_dec_ref(x_99);
 x_108 = lean_box(0);
}
x_109 = l_Lean_registerNamespace(x_102, x_100);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_103);
lean_ctor_set(x_110, 2, x_104);
lean_ctor_set(x_110, 3, x_105);
lean_ctor_set(x_110, 4, x_106);
lean_ctor_set(x_110, 5, x_107);
if (lean_is_scalar(x_101)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_101;
}
lean_ctor_set(x_111, 0, x_96);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_98, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_98, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_114 = x_98;
} else {
 lean_dec_ref(x_98);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Elab_getNamespace___rarg(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
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
x_19 = l_Lean_LocalContext_Inhabited___closed__1;
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
x_34 = l_Lean_LocalContext_Inhabited___closed__1;
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
x_45 = l___private_init_lean_elaborator_command_1__addScopes___main(x_43, x_44, x_40, x_42);
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
x_55 = l___private_init_lean_elaborator_command_1__addScopes___main(x_53, x_54, x_40, x_52);
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
x_75 = l_Lean_LocalContext_Inhabited___closed__1;
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
x_92 = l___private_init_lean_elaborator_command_1__addScopes___main(x_90, x_91, x_82, x_88);
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
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_5);
if (x_96 == 0)
{
return x_5;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_5, 0);
x_98 = lean_ctor_get(x_5, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_5);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
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
lean_object* l___private_init_lean_elaborator_command_2__getNumEndScopes(lean_object* x_1) {
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
lean_object* l___private_init_lean_elaborator_command_2__getNumEndScopes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_init_lean_elaborator_command_2__getNumEndScopes(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l___private_init_lean_elaborator_command_3__checkAnonymousScope(lean_object* x_1) {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_box(0);
x_6 = lean_name_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l___private_init_lean_elaborator_command_3__checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_init_lean_elaborator_command_3__checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_init_lean_elaborator_command_4__checkEndHeader___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_init_lean_elaborator_command_4__checkEndHeader___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_init_lean_elaborator_command_4__checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_init_lean_elaborator_command_4__checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_init_lean_elaborator_command_4__checkEndHeader(x_1, x_2);
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___main___rarg(x_8, x_10);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_array_get(x_12, x_9, x_13);
x_15 = l_Lean_Syntax_getOptionalIdent___rarg(x_14);
lean_dec(x_14);
x_16 = l___private_init_lean_elaborator_command_2__getNumEndScopes(x_15);
x_17 = lean_nat_dec_lt(x_16, x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
x_19 = l_List_drop___main___rarg(x_18, x_8);
lean_dec(x_8);
lean_ctor_set(x_5, 5, x_19);
x_20 = l_Lean_Elab_elabEnd___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
else
{
lean_object* x_21; 
lean_dec(x_11);
x_21 = l_List_drop___main___rarg(x_16, x_8);
lean_ctor_set(x_5, 5, x_21);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_22; 
x_22 = l___private_init_lean_elaborator_command_3__checkAnonymousScope(x_8);
lean_dec(x_8);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Elab_elabEnd___closed__4;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_23);
return x_3;
}
else
{
lean_object* x_24; 
x_24 = lean_box(0);
lean_ctor_set(x_3, 0, x_24);
return x_3;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_25, x_8);
lean_dec(x_8);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Elab_elabEnd___closed__6;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; 
x_28 = lean_box(0);
lean_ctor_set(x_3, 0, x_28);
return x_3;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_List_lengthAux___main___rarg(x_34, x_36);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_array_get(x_38, x_35, x_39);
x_41 = l_Lean_Syntax_getOptionalIdent___rarg(x_40);
lean_dec(x_40);
x_42 = l___private_init_lean_elaborator_command_2__getNumEndScopes(x_41);
x_43 = lean_nat_dec_lt(x_42, x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_41);
x_44 = lean_nat_sub(x_37, x_39);
lean_dec(x_37);
x_45 = l_List_drop___main___rarg(x_44, x_34);
lean_dec(x_34);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_30);
lean_ctor_set(x_46, 2, x_31);
lean_ctor_set(x_46, 3, x_32);
lean_ctor_set(x_46, 4, x_33);
lean_ctor_set(x_46, 5, x_45);
x_47 = l_Lean_Elab_elabEnd___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_46);
lean_ctor_set(x_3, 0, x_47);
return x_3;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
x_48 = l_List_drop___main___rarg(x_42, x_34);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_29);
lean_ctor_set(x_49, 1, x_30);
lean_ctor_set(x_49, 2, x_31);
lean_ctor_set(x_49, 3, x_32);
lean_ctor_set(x_49, 4, x_33);
lean_ctor_set(x_49, 5, x_48);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_50; 
x_50 = l___private_init_lean_elaborator_command_3__checkAnonymousScope(x_34);
lean_dec(x_34);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Lean_Elab_elabEnd___closed__4;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_49);
lean_ctor_set(x_3, 0, x_51);
return x_3;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
lean_ctor_set(x_3, 1, x_49);
lean_ctor_set(x_3, 0, x_52);
return x_3;
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
lean_dec(x_41);
x_54 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_53, x_34);
lean_dec(x_34);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Elab_elabEnd___closed__6;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_49);
lean_ctor_set(x_3, 0, x_55);
return x_3;
}
else
{
lean_object* x_56; 
x_56 = lean_box(0);
lean_ctor_set(x_3, 1, x_49);
lean_ctor_set(x_3, 0, x_56);
return x_3;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
lean_dec(x_3);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 5);
lean_inc(x_63);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 x_64 = x_57;
} else {
 lean_dec_ref(x_57);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_1, 1);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_List_lengthAux___main___rarg(x_63, x_66);
x_68 = lean_box(0);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_array_get(x_68, x_65, x_69);
x_71 = l_Lean_Syntax_getOptionalIdent___rarg(x_70);
lean_dec(x_70);
x_72 = l___private_init_lean_elaborator_command_2__getNumEndScopes(x_71);
x_73 = lean_nat_dec_lt(x_72, x_67);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_72);
lean_dec(x_71);
x_74 = lean_nat_sub(x_67, x_69);
lean_dec(x_67);
x_75 = l_List_drop___main___rarg(x_74, x_63);
lean_dec(x_63);
if (lean_is_scalar(x_64)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_64;
}
lean_ctor_set(x_76, 0, x_58);
lean_ctor_set(x_76, 1, x_59);
lean_ctor_set(x_76, 2, x_60);
lean_ctor_set(x_76, 3, x_61);
lean_ctor_set(x_76, 4, x_62);
lean_ctor_set(x_76, 5, x_75);
x_77 = l_Lean_Elab_elabEnd___closed__2;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_67);
x_79 = l_List_drop___main___rarg(x_72, x_63);
if (lean_is_scalar(x_64)) {
 x_80 = lean_alloc_ctor(0, 6, 0);
} else {
 x_80 = x_64;
}
lean_ctor_set(x_80, 0, x_58);
lean_ctor_set(x_80, 1, x_59);
lean_ctor_set(x_80, 2, x_60);
lean_ctor_set(x_80, 3, x_61);
lean_ctor_set(x_80, 4, x_62);
lean_ctor_set(x_80, 5, x_79);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_81; 
x_81 = l___private_init_lean_elaborator_command_3__checkAnonymousScope(x_63);
lean_dec(x_63);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Lean_Elab_elabEnd___closed__4;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_71, 0);
lean_inc(x_86);
lean_dec(x_71);
x_87 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_86, x_63);
lean_dec(x_63);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_Elab_elabEnd___closed__6;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_80);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_80);
return x_91;
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
lean_object* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_array_fget(x_5, x_6);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_6, x_17);
lean_dec(x_6);
x_19 = l_Lean_Syntax_getId___rarg(x_16);
lean_inc(x_19);
x_20 = l_Lean_Name_append___main(x_2, x_19);
x_21 = l_Lean_Environment_contains(x_4, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = l_Lean_Elab_logUnknownDecl___rarg(x_16, x_20, x_8, x_9);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
x_6 = x_18;
x_9 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_6 = x_18;
x_9 = x_29;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_16);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_9, 0);
lean_dec(x_36);
x_37 = l_Lean_Name_append___main(x_3, x_19);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
x_40 = lean_box(0);
lean_ctor_set(x_9, 0, x_40);
x_6 = x_18;
x_7 = x_39;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_dec(x_9);
x_43 = l_Lean_Name_append___main(x_3, x_19);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
x_6 = x_18;
x_7 = x_45;
x_9 = x_47;
goto _start;
}
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = l_Lean_Elab_getNamespace___rarg(x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_name_dec_eq(x_11, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_ctor_set(x_13, 0, x_12);
x_17 = l_Lean_Elab_getEnv___rarg(x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_17, 0, x_12);
x_20 = lean_box(0);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_array_get(x_5, x_4, x_21);
x_23 = l_Lean_Syntax_getArgs___rarg(x_22);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_11, x_15, x_19, x_23, x_24, x_20, x_2, x_17);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_11);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_27, 0);
x_31 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_30, x_29);
lean_ctor_set(x_27, 0, x_31);
lean_ctor_set(x_25, 0, x_12);
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
x_35 = lean_ctor_get(x_27, 2);
x_36 = lean_ctor_get(x_27, 3);
x_37 = lean_ctor_get(x_27, 4);
x_38 = lean_ctor_get(x_27, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_39 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_33, x_32);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_38);
lean_ctor_set(x_25, 1, x_40);
lean_ctor_set(x_25, 0, x_12);
return x_25;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_25, 1);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
x_50 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_43, x_42);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 6, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_46);
lean_ctor_set(x_51, 4, x_47);
lean_ctor_set(x_51, 5, x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_25, 0);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_17, 0);
x_58 = lean_ctor_get(x_17, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_17);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_box(0);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_array_get(x_5, x_4, x_61);
x_63 = l_Lean_Syntax_getArgs___rarg(x_62);
lean_dec(x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_11, x_15, x_57, x_63, x_64, x_60, x_2, x_59);
lean_dec(x_63);
lean_dec(x_57);
lean_dec(x_15);
lean_dec(x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_66, 5);
lean_inc(x_74);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 lean_ctor_release(x_66, 5);
 x_75 = x_66;
} else {
 lean_dec_ref(x_66);
 x_75 = lean_box(0);
}
x_76 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_69, x_67);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_70);
lean_ctor_set(x_77, 2, x_71);
lean_ctor_set(x_77, 3, x_72);
lean_ctor_set(x_77, 4, x_73);
lean_ctor_set(x_77, 5, x_74);
if (lean_is_scalar(x_68)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_68;
}
lean_ctor_set(x_78, 0, x_12);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_65, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_81 = x_65;
} else {
 lean_dec_ref(x_65);
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
else
{
uint8_t x_83; 
lean_dec(x_15);
lean_dec(x_11);
x_83 = !lean_is_exclusive(x_17);
if (x_83 == 0)
{
return x_17;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_17, 0);
x_85 = lean_ctor_get(x_17, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_17);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_15);
lean_dec(x_11);
x_87 = l_Lean_Elab_elabExport___closed__2;
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_87);
return x_13;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_13, 0);
x_89 = lean_ctor_get(x_13, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_13);
x_90 = lean_name_dec_eq(x_11, x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_12);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_Elab_getEnv___rarg(x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_12);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_box(0);
x_98 = lean_unsigned_to_nat(3u);
x_99 = lean_array_get(x_5, x_4, x_98);
x_100 = l_Lean_Syntax_getArgs___rarg(x_99);
lean_dec(x_99);
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_11, x_88, x_93, x_100, x_101, x_97, x_2, x_96);
lean_dec(x_100);
lean_dec(x_93);
lean_dec(x_88);
lean_dec(x_11);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_103, 4);
lean_inc(x_110);
x_111 = lean_ctor_get(x_103, 5);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
x_113 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_106, x_104);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 6, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set(x_114, 2, x_108);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set(x_114, 4, x_110);
lean_ctor_set(x_114, 5, x_111);
if (lean_is_scalar(x_105)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_105;
}
lean_ctor_set(x_115, 0, x_12);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_102, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_102, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_118 = x_102;
} else {
 lean_dec_ref(x_102);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_88);
lean_dec(x_11);
x_120 = lean_ctor_get(x_92, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_92, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_122 = x_92;
} else {
 lean_dec_ref(x_92);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_88);
lean_dec(x_11);
x_124 = l_Lean_Elab_elabExport___closed__2;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_89);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_11);
x_126 = !lean_is_exclusive(x_13);
if (x_126 == 0)
{
return x_13;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_13, 0);
x_128 = lean_ctor_get(x_13, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_13);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_9, 0);
x_131 = lean_ctor_get(x_9, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_9);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lean_Elab_getNamespace___rarg(x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_138 = lean_name_dec_eq(x_130, x_135);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_136);
x_140 = l_Lean_Elab_getEnv___rarg(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_132);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_box(0);
x_146 = lean_unsigned_to_nat(3u);
x_147 = lean_array_get(x_5, x_4, x_146);
x_148 = l_Lean_Syntax_getArgs___rarg(x_147);
lean_dec(x_147);
x_149 = lean_unsigned_to_nat(0u);
x_150 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_130, x_135, x_141, x_148, x_149, x_145, x_2, x_144);
lean_dec(x_148);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_130);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 4);
lean_inc(x_158);
x_159 = lean_ctor_get(x_151, 5);
lean_inc(x_159);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 lean_ctor_release(x_151, 5);
 x_160 = x_151;
} else {
 lean_dec_ref(x_151);
 x_160 = lean_box(0);
}
x_161 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_154, x_152);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 6, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_155);
lean_ctor_set(x_162, 2, x_156);
lean_ctor_set(x_162, 3, x_157);
lean_ctor_set(x_162, 4, x_158);
lean_ctor_set(x_162, 5, x_159);
if (lean_is_scalar(x_153)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_153;
}
lean_ctor_set(x_163, 0, x_132);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_150, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_150, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_166 = x_150;
} else {
 lean_dec_ref(x_150);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_135);
lean_dec(x_130);
x_168 = lean_ctor_get(x_140, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_140, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_170 = x_140;
} else {
 lean_dec_ref(x_140);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_135);
lean_dec(x_130);
x_172 = l_Lean_Elab_elabExport___closed__2;
if (lean_is_scalar(x_137)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_137;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_136);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_130);
x_174 = lean_ctor_get(x_134, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_134, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_176 = x_134;
} else {
 lean_dec_ref(x_134);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_9);
if (x_178 == 0)
{
return x_9;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_9, 0);
x_180 = lean_ctor_get(x_9, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_9);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 5);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 5);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_7);
x_17 = lean_box(0);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_5, 5);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 4);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_18, 4, x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_5, 5, x_26);
x_27 = lean_box(0);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
x_33 = lean_ctor_get(x_18, 5);
x_34 = lean_ctor_get(x_18, 6);
x_35 = lean_ctor_get(x_18, 7);
x_36 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
lean_ctor_set(x_7, 1, x_32);
lean_ctor_set(x_7, 0, x_1);
x_37 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_7);
lean_ctor_set(x_37, 5, x_33);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_5, 5, x_38);
x_39 = lean_box(0);
lean_ctor_set(x_3, 0, x_39);
return x_3;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_18, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_18, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_18, 7);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_50 = x_18;
} else {
 lean_dec_ref(x_18);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_45);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 8, 1);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set(x_52, 3, x_44);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_46);
lean_ctor_set(x_52, 6, x_47);
lean_ctor_set(x_52, 7, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*8, x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set(x_5, 5, x_53);
x_54 = lean_box(0);
lean_ctor_set(x_3, 0, x_54);
return x_3;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
x_57 = lean_ctor_get(x_5, 2);
x_58 = lean_ctor_get(x_5, 3);
x_59 = lean_ctor_get(x_5, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_60 = lean_ctor_get(x_7, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_61 = x_7;
} else {
 lean_dec_ref(x_7);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_18, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_18, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_18, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_18, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_18, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_18, 6);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 7);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_71 = x_18;
} else {
 lean_dec_ref(x_18);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_61;
}
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_66);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 8, 1);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_63);
lean_ctor_set(x_73, 2, x_64);
lean_ctor_set(x_73, 3, x_65);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_67);
lean_ctor_set(x_73, 6, x_68);
lean_ctor_set(x_73, 7, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*8, x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_55);
lean_ctor_set(x_75, 1, x_56);
lean_ctor_set(x_75, 2, x_57);
lean_ctor_set(x_75, 3, x_58);
lean_ctor_set(x_75, 4, x_59);
lean_ctor_set(x_75, 5, x_74);
x_76 = lean_box(0);
lean_ctor_set(x_3, 1, x_75);
lean_ctor_set(x_3, 0, x_76);
return x_3;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_dec(x_3);
x_78 = lean_ctor_get(x_77, 5);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 4);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 6, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_80);
lean_ctor_set(x_85, 2, x_81);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set(x_85, 4, x_83);
lean_ctor_set(x_85, 5, x_78);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_77, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_77, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_77, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_77, 4);
lean_inc(x_93);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_94 = x_77;
} else {
 lean_dec_ref(x_77);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_96 = x_78;
} else {
 lean_dec_ref(x_78);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_88, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_88, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_88, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_88, 7);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_88, sizeof(void*)*8);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 lean_ctor_release(x_88, 6);
 lean_ctor_release(x_88, 7);
 x_106 = x_88;
} else {
 lean_dec_ref(x_88);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_96;
}
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_101);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 8, 1);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_98);
lean_ctor_set(x_108, 2, x_99);
lean_ctor_set(x_108, 3, x_100);
lean_ctor_set(x_108, 4, x_107);
lean_ctor_set(x_108, 5, x_102);
lean_ctor_set(x_108, 6, x_103);
lean_ctor_set(x_108, 7, x_104);
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_95);
if (lean_is_scalar(x_94)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_94;
}
lean_ctor_set(x_110, 0, x_89);
lean_ctor_set(x_110, 1, x_90);
lean_ctor_set(x_110, 2, x_91);
lean_ctor_set(x_110, 3, x_92);
lean_ctor_set(x_110, 4, x_93);
lean_ctor_set(x_110, 5, x_109);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
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
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_array_fget(x_2, x_3);
x_14 = l_Lean_Syntax_getId___rarg(x_13);
lean_dec(x_13);
x_15 = l_Lean_Elab_resolveNamespace(x_14, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_20, x_5, x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_21, 0, x_18);
x_24 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_24;
x_4 = x_23;
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_29;
x_4 = x_26;
x_6 = x_28;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_40, x_5, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_46;
x_4 = x_42;
x_6 = x_45;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_50 = x_41;
} else {
 lean_dec_ref(x_41);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_15);
if (x_52 == 0)
{
return x_15;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_15, 0);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_15);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
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
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_14 = lean_array_fget(x_3, x_4);
x_15 = l_Lean_Syntax_getId___rarg(x_14);
lean_inc(x_15);
x_16 = l_Lean_Name_append___main(x_1, x_15);
x_17 = l_Lean_Elab_getEnv___rarg(x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
x_21 = l_Lean_Environment_contains(x_19, x_16);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_15);
x_22 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_16, x_6, x_17);
lean_dec(x_14);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_22, 0, x_20);
x_25 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_25;
x_5 = x_24;
x_7 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_30;
x_5 = x_27;
x_7 = x_29;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_16);
x_37 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_36, x_6, x_17);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_ctor_set(x_37, 0, x_20);
x_40 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_40;
x_5 = x_39;
x_7 = x_37;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_20);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_45;
x_5 = x_42;
x_7 = x_44;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_37);
if (x_47 == 0)
{
return x_37;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_37, 0);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_37);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Environment_contains(x_51, x_16);
lean_dec(x_51);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_15);
x_56 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_16, x_6, x_54);
lean_dec(x_14);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_61;
x_5 = x_57;
x_7 = x_60;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_4);
x_63 = lean_ctor_get(x_56, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_65 = x_56;
} else {
 lean_dec_ref(x_56);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_14);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_15);
lean_ctor_set(x_67, 1, x_16);
x_68 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_67, x_6, x_54);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_53);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_73;
x_5 = x_69;
x_7 = x_72;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_4);
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_77 = x_68;
} else {
 lean_dec_ref(x_68);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_17);
if (x_79 == 0)
{
return x_17;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_17, 0);
x_81 = lean_ctor_get(x_17, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_17);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_array_get(x_5, x_4, x_13);
x_15 = l_Lean_Syntax_getArgs___rarg(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_11, x_16, x_15, x_6, x_12, x_2, x_9);
lean_dec(x_15);
lean_dec(x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_array_get(x_5, x_4, x_22);
x_24 = l_Lean_Syntax_getArgs___rarg(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_18, x_25, x_24, x_6, x_20, x_2, x_21);
lean_dec(x_24);
lean_dec(x_18);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
uint8_t x_11; 
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_fget(x_4, x_5);
x_16 = l_Lean_Syntax_getId___rarg(x_15);
lean_inc(x_16);
x_17 = l_Lean_Name_append___main(x_1, x_16);
x_18 = l_Lean_Environment_contains(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = l_Lean_Elab_logUnknownDecl___rarg(x_15, x_17, x_7, x_8);
lean_dec(x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
x_23 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_23;
x_8 = x_19;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_28;
x_8 = x_27;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_15);
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_8, 0);
lean_dec(x_35);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_6);
x_37 = lean_box(0);
lean_ctor_set(x_8, 0, x_37);
x_38 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_38;
x_6 = x_36;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_6);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_44 = lean_nat_add(x_5, x_3);
lean_dec(x_5);
x_5 = x_44;
x_6 = x_41;
x_8 = x_43;
goto _start;
}
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = l_Lean_Elab_getEnv___rarg(x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_array_get(x_5, x_4, x_16);
lean_ctor_set(x_13, 0, x_12);
x_18 = lean_box(0);
x_19 = l_Lean_Syntax_getArgs___rarg(x_17);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_11, x_15, x_20, x_19, x_6, x_18, x_2, x_13);
lean_dec(x_19);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_21, 0, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_24, x_2, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_26);
x_30 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_29, x_2, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_array_get(x_5, x_4, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_box(0);
x_41 = l_Lean_Syntax_getArgs___rarg(x_38);
lean_dec(x_38);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_11, x_35, x_42, x_41, x_6, x_40, x_2, x_39);
lean_dec(x_41);
lean_dec(x_35);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_44);
x_49 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_48, x_2, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_11);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_11);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_9, 0);
x_59 = lean_ctor_get(x_9, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_9);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Elab_getEnv___rarg(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_unsigned_to_nat(2u);
x_67 = lean_array_get(x_5, x_4, x_66);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_64);
x_69 = lean_box(0);
x_70 = l_Lean_Syntax_getArgs___rarg(x_67);
lean_dec(x_67);
x_71 = lean_unsigned_to_nat(1u);
x_72 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_58, x_63, x_71, x_70, x_6, x_69, x_2, x_68);
lean_dec(x_70);
lean_dec(x_63);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_60);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_58);
lean_ctor_set(x_77, 1, x_73);
x_78 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_77, x_2, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_58);
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_81 = x_72;
} else {
 lean_dec_ref(x_72);
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
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_58);
x_83 = lean_ctor_get(x_62, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_62, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_85 = x_62;
} else {
 lean_dec_ref(x_62);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_9);
if (x_87 == 0)
{
return x_9;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_9, 0);
x_89 = lean_ctor_get(x_9, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_9);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
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
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getIdAt___rarg(x_14, x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getIdAt___rarg(x_14, x_17);
x_19 = l_Lean_Name_append___main(x_1, x_16);
x_20 = l_Lean_Elab_getEnv___rarg(x_7);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
x_24 = l_Lean_Environment_contains(x_22, x_19);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_18);
x_25 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_19, x_6, x_20);
lean_dec(x_14);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_25, 0, x_23);
x_28 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_28;
x_5 = x_27;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_33;
x_5 = x_30;
x_7 = x_32;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_19);
x_40 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_39, x_6, x_20);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_ctor_set(x_40, 0, x_23);
x_43 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_43;
x_5 = x_42;
x_7 = x_40;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_23);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_48;
x_5 = x_45;
x_7 = x_47;
goto _start;
}
}
else
{
uint8_t x_50; 
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_40);
if (x_50 == 0)
{
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_40);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_20, 0);
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_20);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Environment_contains(x_54, x_19);
lean_dec(x_54);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_18);
x_59 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_19, x_6, x_57);
lean_dec(x_14);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_64;
x_5 = x_60;
x_7 = x_63;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_4);
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_14);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_19);
x_71 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_70, x_6, x_57);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_76;
x_5 = x_72;
x_7 = x_75;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_4);
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_71, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_80 = x_71;
} else {
 lean_dec_ref(x_71);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_20);
if (x_82 == 0)
{
return x_20;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_20, 0);
x_84 = lean_ctor_get(x_20, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_20);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_array_get(x_5, x_4, x_13);
x_15 = l_Lean_Syntax_getArgs___rarg(x_14);
lean_dec(x_14);
x_16 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_11, x_13, x_15, x_6, x_12, x_2, x_9);
lean_dec(x_15);
lean_dec(x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_array_get(x_5, x_4, x_21);
x_23 = l_Lean_Syntax_getArgs___rarg(x_22);
lean_dec(x_22);
x_24 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_17, x_21, x_23, x_6, x_19, x_2, x_20);
lean_dec(x_23);
lean_dec(x_17);
return x_24;
}
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
x_11 = lean_name_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
x_13 = lean_name_dec_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
x_15 = lean_name_dec_eq(x_9, x_14);
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_5, 5);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 5);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_7);
x_17 = lean_box(0);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_5, 5);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 5);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_18, 5, x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_5, 5, x_26);
x_27 = lean_box(0);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
x_33 = lean_ctor_get(x_18, 5);
x_34 = lean_ctor_get(x_18, 6);
x_35 = lean_ctor_get(x_18, 7);
x_36 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
lean_ctor_set(x_7, 1, x_33);
lean_ctor_set(x_7, 0, x_1);
x_37 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_37, 5, x_7);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_5, 5, x_38);
x_39 = lean_box(0);
lean_ctor_set(x_3, 0, x_39);
return x_3;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_18, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_18, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_18, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_18, 7);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_50 = x_18;
} else {
 lean_dec_ref(x_18);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_46);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 8, 1);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set(x_52, 3, x_44);
lean_ctor_set(x_52, 4, x_45);
lean_ctor_set(x_52, 5, x_51);
lean_ctor_set(x_52, 6, x_47);
lean_ctor_set(x_52, 7, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*8, x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_40);
lean_ctor_set(x_5, 5, x_53);
x_54 = lean_box(0);
lean_ctor_set(x_3, 0, x_54);
return x_3;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
x_57 = lean_ctor_get(x_5, 2);
x_58 = lean_ctor_get(x_5, 3);
x_59 = lean_ctor_get(x_5, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_60 = lean_ctor_get(x_7, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_61 = x_7;
} else {
 lean_dec_ref(x_7);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_18, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_18, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_18, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_18, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_18, 5);
lean_inc(x_67);
x_68 = lean_ctor_get(x_18, 6);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 7);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_71 = x_18;
} else {
 lean_dec_ref(x_18);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_61;
}
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_67);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 8, 1);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_63);
lean_ctor_set(x_73, 2, x_64);
lean_ctor_set(x_73, 3, x_65);
lean_ctor_set(x_73, 4, x_66);
lean_ctor_set(x_73, 5, x_72);
lean_ctor_set(x_73, 6, x_68);
lean_ctor_set(x_73, 7, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*8, x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_55);
lean_ctor_set(x_75, 1, x_56);
lean_ctor_set(x_75, 2, x_57);
lean_ctor_set(x_75, 3, x_58);
lean_ctor_set(x_75, 4, x_59);
lean_ctor_set(x_75, 5, x_74);
x_76 = lean_box(0);
lean_ctor_set(x_3, 1, x_75);
lean_ctor_set(x_3, 0, x_76);
return x_3;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_dec(x_3);
x_78 = lean_ctor_get(x_77, 5);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 4);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 6, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_80);
lean_ctor_set(x_85, 2, x_81);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set(x_85, 4, x_83);
lean_ctor_set(x_85, 5, x_78);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_77, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_77, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_77, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_77, 4);
lean_inc(x_93);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_94 = x_77;
} else {
 lean_dec_ref(x_77);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_96 = x_78;
} else {
 lean_dec_ref(x_78);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_88, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_88, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_88, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_88, 7);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_88, sizeof(void*)*8);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 lean_ctor_release(x_88, 6);
 lean_ctor_release(x_88, 7);
 x_106 = x_88;
} else {
 lean_dec_ref(x_88);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_96;
}
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_102);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 8, 1);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_98);
lean_ctor_set(x_108, 2, x_99);
lean_ctor_set(x_108, 3, x_100);
lean_ctor_set(x_108, 4, x_101);
lean_ctor_set(x_108, 5, x_107);
lean_ctor_set(x_108, 6, x_103);
lean_ctor_set(x_108, 7, x_104);
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_95);
if (lean_is_scalar(x_94)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_94;
}
lean_ctor_set(x_110, 0, x_89);
lean_ctor_set(x_110, 1, x_90);
lean_ctor_set(x_110, 2, x_91);
lean_ctor_set(x_110, 3, x_92);
lean_ctor_set(x_110, 4, x_93);
lean_ctor_set(x_110, 5, x_109);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
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
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Syntax_getId___rarg(x_1);
x_5 = l_Lean_Elab_getUniverses___rarg(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
x_9 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_4, x_7);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_4, x_2, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_4);
x_13 = l_Lean_Elab_addUniverse___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_Elab_addUniverse___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_Elab_logError___rarg(x_1, x_16, x_2, x_5);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_4, x_18);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_4, x_2, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_4);
x_26 = l_Lean_Elab_addUniverse___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lean_Elab_addUniverse___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_Elab_logError___rarg(x_1, x_29, x_2, x_21);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
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
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_fget(x_2, x_3);
x_14 = l_Lean_Elab_addUniverse(x_13, x_5, x_6);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
x_18 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_18;
x_4 = x_16;
x_6 = x_14;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_24;
x_4 = x_20;
x_6 = x_23;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
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
lean_object* x_3; 
x_3 = l_Lean_Elab_getEnv___rarg(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_box(4);
x_8 = lean_add_decl(x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Elab_logElabException(x_10, x_1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Elab_setEnv(x_12, x_1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_box(4);
x_19 = lean_add_decl(x_14, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Elab_logElabException(x_21, x_1, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Elab_setEnv(x_23, x_1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
return x_3;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
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
x_4 = lean_alloc_closure((void*)(l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1), 2, 1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Elab_resolveName(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = lean_box(0);
x_14 = l_Lean_Elab_getPosition(x_13, x_2, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_12);
x_17 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Nat_repr(x_18);
x_21 = l_Sigma_HasRepr___rarg___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_List_reprAux___main___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Nat_repr(x_19);
x_26 = lean_string_append(x_24, x_25);
lean_dec(x_25);
x_27 = l_Sigma_HasRepr___rarg___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_String_Iterator_HasRepr___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_17);
lean_dec(x_17);
x_32 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_runIOUnsafe___rarg(x_32, x_2, x_14);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_12);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_11);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l_Nat_repr(x_46);
x_49 = l_Sigma_HasRepr___rarg___closed__1;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l_List_reprAux___main___rarg___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = l_Nat_repr(x_47);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = l_Sigma_HasRepr___rarg___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_String_Iterator_HasRepr___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_45);
lean_dec(x_45);
x_60 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = l_Lean_Elab_runIOUnsafe___rarg(x_60, x_2, x_44);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_11);
x_69 = !lean_is_exclusive(x_14);
if (x_69 == 0)
{
return x_14;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_14, 0);
x_71 = lean_ctor_get(x_14, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_14);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_9, 0);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_9);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_box(0);
x_78 = l_Lean_Elab_getPosition(x_77, x_2, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_73);
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_86 = l_Nat_repr(x_84);
x_87 = l_Sigma_HasRepr___rarg___closed__1;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
x_89 = l_List_reprAux___main___rarg___closed__1;
x_90 = lean_string_append(x_88, x_89);
x_91 = l_Nat_repr(x_85);
x_92 = lean_string_append(x_90, x_91);
lean_dec(x_91);
x_93 = l_Sigma_HasRepr___rarg___closed__2;
x_94 = lean_string_append(x_92, x_93);
x_95 = l_String_Iterator_HasRepr___closed__2;
x_96 = lean_string_append(x_94, x_95);
x_97 = lean_string_append(x_96, x_83);
lean_dec(x_83);
x_98 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_98, 0, x_97);
x_99 = l_Lean_Elab_runIOUnsafe___rarg(x_98, x_2, x_82);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_75);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_105 = x_99;
} else {
 lean_dec_ref(x_99);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_73);
x_107 = lean_ctor_get(x_78, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_78, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_109 = x_78;
} else {
 lean_dec_ref(x_78);
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
else
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_9);
if (x_111 == 0)
{
return x_9;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_9, 0);
x_113 = lean_ctor_get(x_9, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_9);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
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
x_8 = lean_alloc_closure((void*)(l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_runIOUnsafe___rarg(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
x_13 = x_7;
lean_inc(x_2);
x_14 = l_Lean_Elab_toPreTerm(x_13, x_2, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_12);
x_17 = lean_expr_dbg_to_string(x_16);
lean_dec(x_16);
x_18 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_runIOUnsafe___rarg(x_18, x_2, x_14);
lean_dec(x_2);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
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
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_expr_dbg_to_string(x_28);
lean_dec(x_28);
x_32 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_runIOUnsafe___rarg(x_32, x_2, x_30);
lean_dec(x_2);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_39 = x_33;
} else {
 lean_dec_ref(x_33);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
return x_14;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_dec(x_9);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = x_7;
lean_inc(x_2);
x_49 = l_Lean_Elab_toPreTerm(x_48, x_2, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_expr_dbg_to_string(x_50);
lean_dec(x_50);
x_55 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = l_Lean_Elab_runIOUnsafe___rarg(x_55, x_2, x_53);
lean_dec(x_2);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_46);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_49, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_66 = x_49;
} else {
 lean_dec_ref(x_49);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_7);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_9);
if (x_68 == 0)
{
return x_9;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_IO_println___rarg___closed__1;
x_8 = lean_io_prim_put_str(x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_IO_println___rarg___closed__1;
x_13 = lean_io_prim_put_str(x_12, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_expr_dbg_to_string(x_29);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = l_Lean_Elab_runIOUnsafe___rarg(x_31, x_2, x_11);
lean_dec(x_2);
return x_32;
}
else
{
x_15 = x_14;
goto block_28;
}
block_28:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_15);
x_16 = lean_alloc_closure((void*)(l_IO_println___at_Lean_Elab_elabElab___spec__1), 2, 1);
lean_closure_set(x_16, 0, x_13);
x_17 = l_Lean_Elab_runIOUnsafe___rarg(x_16, x_2, x_11);
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
x_20 = l_Lean_Elab_elabElab___closed__2;
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Elab_elabElab___closed__2;
x_23 = lean_alloc_ctor(1, 2, 0);
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
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_33, 0);
lean_inc(x_49);
lean_dec(x_33);
x_50 = lean_expr_dbg_to_string(x_49);
lean_dec(x_49);
x_51 = lean_alloc_closure((void*)(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean_closure_set(x_51, 0, x_50);
x_52 = l_Lean_Elab_runIOUnsafe___rarg(x_51, x_2, x_36);
lean_dec(x_2);
return x_52;
}
else
{
x_37 = x_35;
goto block_48;
}
block_48:
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_37);
x_38 = lean_alloc_closure((void*)(l_IO_println___at_Lean_Elab_elabElab___spec__1), 2, 1);
lean_closure_set(x_38, 0, x_33);
x_39 = l_Lean_Elab_runIOUnsafe___rarg(x_38, x_2, x_36);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Elab_elabElab___closed__2;
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_41;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_46 = x_39;
} else {
 lean_dec_ref(x_39);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_11);
if (x_53 == 0)
{
return x_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
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
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
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
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
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
lean_object* initialize_init_lean_elaborator_alias(lean_object*);
lean_object* initialize_init_lean_elaborator_basic(lean_object*);
lean_object* initialize_init_lean_elaborator_resolvename(lean_object*);
lean_object* initialize_init_lean_elaborator_term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_elaborator_command(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_alias(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_resolvename(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_term(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabNamespace(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabSection(w);
if (lean_io_result_is_error(w)) return w;
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
w = l___regBuiltinTermElab_Lean_Elab_elabEnd(w);
if (lean_io_result_is_error(w)) return w;
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
w = l___regBuiltinTermElab_Lean_Elab_elabExport(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabOpen(w);
if (lean_io_result_is_error(w)) return w;
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
w = l___regBuiltinTermElab_Lean_Elab_elabUniverse(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabUniverses(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabInitQuot(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabVariable(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabResolveName(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabPreTerm(w);
if (lean_io_result_is_error(w)) return w;
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
w = l___regBuiltinTermElab_Lean_Elab_elabElab(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabMixfix(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabReserve(w);
if (lean_io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabNotation(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
