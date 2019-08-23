// Lean compiler output
// Module: init.lean.elaborator.command
// Imports: init.lean.elaborator.alias init.lean.elaborator.basic init.lean.elaborator.resolvename init.lean.elaborator.term
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" {
obj* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3;
obj* l_Lean_Elab_elabNotation___rarg(obj*);
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabEnd(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_elabSection(obj*);
obj* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1___boxed(obj*, obj*, obj*);
uint8 lean_name_dec_eq(obj*, obj*);
obj* l___private_init_lean_elaborator_command_4__checkEndHeader___main___boxed(obj*, obj*);
obj* l_Lean_Elab_addOpenDecl(obj*, obj*, obj*);
obj* l_Lean_Elab_elabOpenSimple(obj*, obj*, obj*);
obj* l_Lean_Elab_elabSection(obj*, obj*, obj*);
obj* l___private_init_lean_elaborator_command_1__addScopes___main___boxed(obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1;
obj* lean_nat_sub(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3;
obj* l_Lean_Elab_elabInitQuot___rarg___boxed(obj*, obj*);
extern obj* l_Sigma_HasRepr___rarg___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1;
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_runIOUnsafe___rarg(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2;
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2;
obj* l_IO_println___at_HasRepr_HasEval___spec__1___boxed(obj*, obj*);
extern obj* l_List_repr___rarg___closed__3;
extern obj* l_Lean_Parser_Command_variable___elambda__1___closed__2;
obj* l_Lean_Elab_elabEnd___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_elabOpen(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2;
extern obj* l_Lean_Parser_Command_export___elambda__1___closed__2;
obj* l_List_lengthAux___main___rarg(obj*, obj*);
obj* lean_expr_dbg_to_string(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1;
obj* l_Lean_Elab_elabEnd___closed__4;
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2;
obj* lean_add_decl(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3;
extern obj* l_Lean_LocalContext_Inhabited___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_elabInitQuot(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabMixfix(obj*);
obj* l_Lean_Elab_elabExport___boxed(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabElab(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2;
obj* l_Lean_Elab_addUniverse___closed__2;
extern obj* l_Lean_Parser_Command_elab___elambda__1___rarg___closed__2;
obj* l_Lean_Elab_logError___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_elabSection___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(obj*, obj*, obj*);
obj* l_Lean_Elab_elabOpenHiding(obj*, obj*, obj*);
obj* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(uint8, obj*);
obj* l_Lean_Elab_elabResolveName(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2;
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_addBuiltinCommandElab(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_asNode___rarg(obj*);
obj* l_Lean_Elab_elabInitQuot(obj*);
obj* l_List_head___at_Lean_Elab_getScope___spec__1(obj*);
obj* l_Lean_Elab_elabElab(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1;
obj* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1___boxed(obj*, obj*, obj*);
uint8 l___private_init_lean_elaborator_command_3__checkAnonymousScope(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabOpen(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverse(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3;
extern obj* l_Lean_Parser_Command_preterm___elambda__1___rarg___closed__2;
obj* l_Lean_Elab_addUniverse___closed__1;
obj* l_Lean_Elab_elabOpenOnly___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_addUniverse(obj*, obj*, obj*);
obj* l_Lean_Elab_elabVariable(obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
obj* l_Lean_Elab_addOpenDecl___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_elabMixfix___boxed(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3;
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverses(obj*);
obj* l_Lean_Elab_elabUniverses(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3;
obj* l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3;
obj* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3;
obj* l___regBuiltinTermElab_Lean_Elab_elabNotation(obj*);
obj* l___private_init_lean_elaborator_command_1__addScopes(obj*, uint8, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1;
obj* l_Lean_Elab_elabNamespace___boxed(obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(obj*, obj*);
obj* l___private_init_lean_elaborator_command_3__checkAnonymousScope___boxed(obj*);
obj* l_Lean_Elab_resolveNamespace(obj*, obj*, obj*);
obj* l_Lean_Elab_elabMixfix___rarg(obj*);
obj* l_Lean_Syntax_lift(obj*, obj*);
obj* l_Lean_Elab_setEnv(obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
extern obj* l_List_repr___rarg___closed__2;
obj* l_Lean_Elab_getNamespace___rarg(obj*);
obj* l_Lean_Elab_elabOpenRenaming(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
extern obj* l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
obj* l_Lean_addAlias(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Command_universes___elambda__1___closed__2;
obj* l___private_init_lean_elaborator_command_1__addScopes___main(obj*, uint8, obj*, obj*);
obj* l_Lean_Elab_elabVariable___boxed(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1;
uint8 l___private_init_lean_elaborator_command_4__checkEndHeader___main(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabReserve(obj*);
obj* l_Lean_Elab_elabElab___boxed(obj*, obj*, obj*);
obj* lean_string_append(obj*, obj*);
obj* l_List_drop___main___rarg(obj*, obj*);
obj* l_Lean_Elab_elabExport___closed__1;
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_Lean_Elab_addUniverse___boxed(obj*, obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2;
uint8 lean_nat_dec_lt(obj*, obj*);
obj* l_Lean_Elab_elabElab___closed__2;
obj* l_Lean_Elab_elabExport___closed__2;
obj* l_Lean_Syntax_getArgs___rarg(obj*);
obj* l_Lean_Elab_elabEnd___closed__2;
obj* l_Lean_Syntax_getId___rarg(obj*);
obj* l_Lean_Elab_elabExport(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Command_resolve__name___elambda__1___rarg___closed__2;
extern obj* l_Lean_Parser_Command_notation___elambda__1___closed__2;
obj* l___private_init_lean_elaborator_command_1__addScopes___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_getUniverses___rarg(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* lean_name_mk_string(obj*, obj*);
obj* lean_nat_add(obj*, obj*);
extern obj* l_Lean_Parser_Command_open___elambda__1___closed__2;
obj* l_Lean_Elab_elabOpen___boxed(obj*, obj*, obj*);
extern obj* l_Prod_HasRepr___rarg___closed__1;
extern obj* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__2;
extern obj* l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
extern obj* l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
obj* l_Lean_Elab_elabNamespace(obj*, obj*, obj*);
obj* l_Lean_Elab_modifyScope(obj*, obj*, obj*);
obj* l_Lean_Elab_elabOpenSimple___boxed(obj*, obj*, obj*);
extern obj* l_Lean_Format_flatten___main___closed__1;
obj* l_Lean_Elab_resolveName(obj*, obj*, obj*);
obj* l_Lean_Name_getNumParts___main(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3;
obj* l_Lean_Elab_elabNotation___boxed(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3;
obj* l_Lean_Elab_elabEnd___closed__6;
uint8 l_Lean_Name_eqStr(obj*, obj*);
obj* l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabVariable(obj*);
obj* l_Lean_Elab_logUnknownDecl___rarg(obj*, obj*, obj*, obj*);
uint8 l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(obj*, obj*);
obj* l_Lean_Elab_elabUniverses___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_elabPreTerm___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Sigma_HasRepr___rarg___closed__2;
obj* l_Lean_Elab_elabTermAux___main(obj*, obj*, uint8, obj*, obj*);
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_elabInitQuot___rarg(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2;
obj* l_Lean_registerNamespace(obj*, obj*);
obj* l_Lean_Elab_elabReserve___rarg(obj*);
obj* l___private_init_lean_elaborator_command_2__getNumEndScopes___boxed(obj*);
obj* l___private_init_lean_elaborator_command_2__getNumEndScopes(obj*);
obj* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getIdAt___rarg(obj*, obj*);
obj* l_Lean_Elab_elabUniverse___boxed(obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1;
obj* l_List_toString___at_Lean_Elab_elabResolveName___spec__1(obj*);
obj* l_Lean_Elab_elabEnd(obj*, obj*, obj*);
obj* l_Lean_Elab_toPreTerm(obj*, obj*, obj*);
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_elabEnd___closed__5;
obj* l_Lean_Elab_getEnv___rarg(obj*);
obj* l_Array_size(obj*, obj*);
extern obj* l_Lean_Parser_Command_section___elambda__1___rarg___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2;
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Lean_Elab_elabElab___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabExport(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_elabResolveName(obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3;
obj* l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabNamespace(obj*);
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1;
obj* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3;
obj* l_Lean_Elab_getPosition(obj*, obj*, obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l___private_init_lean_elaborator_command_4__checkEndHeader___boxed(obj*, obj*);
uint8 l_Lean_Environment_contains(obj*, obj*);
obj* l_Lean_Elab_elabEnd___closed__3;
extern obj* l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
obj* l_Lean_Elab_elabResolveName___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_elabOpenOnly(obj*, obj*, obj*);
extern obj* l_Lean_Parser_Command_init__quot___elambda__1___rarg___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3;
obj* l_Lean_Elab_elabEnd___closed__1;
obj* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2___boxed(obj*, obj*);
extern obj* l_Lean_Parser_Command_reserve___elambda__1___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1;
obj* l_Lean_Elab_logElabException(obj*, obj*, obj*);
obj* l_Lean_Elab_elabInitQuot___boxed(obj*);
obj* l_Lean_Elab_elabMixfix(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1;
uint8 l___private_init_lean_elaborator_command_4__checkEndHeader(obj*, obj*);
obj* l_Lean_Elab_elabOpenHiding___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_elabPreTerm(obj*, obj*, obj*);
obj* l_Lean_Elab_elabNotation(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabPreTerm(obj*);
obj* l_Lean_Elab_modifyScope___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_elabReserve(obj*, obj*);
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getOptionalIdent___rarg(obj*);
extern obj* l_Lean_Parser_Command_end___elambda__1___rarg___closed__2;
obj* l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2;
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3;
extern obj* l_Lean_Parser_Command_universe___elambda__1___rarg___closed__2;
extern obj* l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
obj* l_Lean_Elab_elabUniverse(obj*, obj*, obj*);
obj* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(obj*, obj*, obj*);
extern obj* l_List_repr___rarg___closed__1;
obj* l_Lean_Elab_elabOpenRenaming___boxed(obj*, obj*, obj*);
obj* l_Lean_Elab_elabReserve___boxed(obj*, obj*);
obj* l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1;
extern obj* l_String_splitAux___main___closed__1;
obj* l___private_init_lean_elaborator_command_1__addScopes___main(obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
switch (lean::obj_tag(x_3)) {
case 0:
{
lean::dec(x_1);
lean::inc(x_4);
return x_4;
}
case 1:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
x_7 = l___private_init_lean_elaborator_command_1__addScopes___main(x_1, x_2, x_5, x_4);
x_8 = l_List_head___at_Lean_Elab_getScope___spec__1(x_7);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = lean::cnstr_get(x_8, 3);
x_11 = lean::cnstr_get(x_8, 6);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_8, 5);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_8, 4);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_8, 2);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_8, 1);
lean::dec(x_15);
x_16 = lean::cnstr_get(x_8, 0);
lean::dec(x_16);
x_17 = lean::box(0);
lean::inc(x_6);
x_18 = lean_name_mk_string(x_17, x_6);
x_19 = lean::box(0);
if (x_2 == 0)
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_6);
x_20 = l_Lean_Options_empty;
x_21 = l_Lean_LocalContext_Inhabited___closed__1;
lean::cnstr_set(x_8, 6, x_21);
lean::cnstr_set(x_8, 5, x_19);
lean::cnstr_set(x_8, 4, x_19);
lean::cnstr_set(x_8, 2, x_20);
lean::cnstr_set(x_8, 1, x_18);
lean::cnstr_set(x_8, 0, x_1);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_8);
lean::cnstr_set(x_22, 1, x_7);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean_name_mk_string(x_10, x_6);
x_24 = l_Lean_Options_empty;
x_25 = l_Lean_LocalContext_Inhabited___closed__1;
lean::cnstr_set(x_8, 6, x_25);
lean::cnstr_set(x_8, 5, x_19);
lean::cnstr_set(x_8, 4, x_19);
lean::cnstr_set(x_8, 3, x_23);
lean::cnstr_set(x_8, 2, x_24);
lean::cnstr_set(x_8, 1, x_18);
lean::cnstr_set(x_8, 0, x_1);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_8);
lean::cnstr_set(x_26, 1, x_7);
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_27 = lean::cnstr_get(x_8, 3);
lean::inc(x_27);
lean::dec(x_8);
x_28 = lean::box(0);
lean::inc(x_6);
x_29 = lean_name_mk_string(x_28, x_6);
x_30 = lean::box(0);
if (x_2 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_6);
x_31 = l_Lean_Options_empty;
x_32 = l_Lean_LocalContext_Inhabited___closed__1;
x_33 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_29);
lean::cnstr_set(x_33, 2, x_31);
lean::cnstr_set(x_33, 3, x_27);
lean::cnstr_set(x_33, 4, x_30);
lean::cnstr_set(x_33, 5, x_30);
lean::cnstr_set(x_33, 6, x_32);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_7);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_35 = lean_name_mk_string(x_27, x_6);
x_36 = l_Lean_Options_empty;
x_37 = l_Lean_LocalContext_Inhabited___closed__1;
x_38 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_29);
lean::cnstr_set(x_38, 2, x_36);
lean::cnstr_set(x_38, 3, x_35);
lean::cnstr_set(x_38, 4, x_30);
lean::cnstr_set(x_38, 5, x_30);
lean::cnstr_set(x_38, 6, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_7);
return x_39;
}
}
}
default: 
{
obj* x_40; 
lean::dec(x_3);
lean::dec(x_1);
x_40 = lean::box(0);
return x_40;
}
}
}
}
obj* l___private_init_lean_elaborator_command_1__addScopes___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
lean::dec(x_2);
x_6 = l___private_init_lean_elaborator_command_1__addScopes___main(x_1, x_5, x_3, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l___private_init_lean_elaborator_command_1__addScopes(obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_elaborator_command_1__addScopes___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_elaborator_command_1__addScopes___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
lean::dec(x_2);
x_6 = l___private_init_lean_elaborator_command_1__addScopes(x_1, x_5, x_3, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Elab_elabNamespace(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = lean::box(0);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean_array_get(x_8, x_5, x_9);
x_11 = l_Lean_Syntax_getId___rarg(x_10);
lean::dec(x_10);
x_12 = !lean::is_exclusive(x_6);
if (x_12 == 0)
{
obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_6, 5);
x_14 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_15 = 1;
x_16 = l___private_init_lean_elaborator_command_1__addScopes___main(x_14, x_15, x_11, x_13);
lean::dec(x_13);
lean::cnstr_set(x_6, 5, x_16);
x_17 = lean::box(0);
lean::cnstr_set(x_3, 0, x_17);
x_18 = l_Lean_Elab_getNamespace___rarg(x_3);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = lean::cnstr_get(x_18, 1);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_18, 0);
x_23 = lean::cnstr_get(x_20, 0);
x_24 = l_Lean_registerNamespace(x_23, x_22);
lean::cnstr_set(x_20, 0, x_24);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_18, 0);
x_26 = lean::cnstr_get(x_20, 0);
x_27 = lean::cnstr_get(x_20, 1);
x_28 = lean::cnstr_get(x_20, 2);
x_29 = lean::cnstr_get(x_20, 3);
x_30 = lean::cnstr_get(x_20, 4);
x_31 = lean::cnstr_get(x_20, 5);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_20);
x_32 = l_Lean_registerNamespace(x_26, x_25);
x_33 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_27);
lean::cnstr_set(x_33, 2, x_28);
lean::cnstr_set(x_33, 3, x_29);
lean::cnstr_set(x_33, 4, x_30);
lean::cnstr_set(x_33, 5, x_31);
lean::cnstr_set(x_18, 1, x_33);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_34 = lean::cnstr_get(x_18, 1);
x_35 = lean::cnstr_get(x_18, 0);
lean::inc(x_34);
lean::inc(x_35);
lean::dec(x_18);
x_36 = lean::cnstr_get(x_34, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_34, 2);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_34, 3);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_34, 4);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_34, 5);
lean::inc(x_41);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 lean::cnstr_release(x_34, 2);
 lean::cnstr_release(x_34, 3);
 lean::cnstr_release(x_34, 4);
 lean::cnstr_release(x_34, 5);
 x_42 = x_34;
} else {
 lean::dec_ref(x_34);
 x_42 = lean::box(0);
}
x_43 = l_Lean_registerNamespace(x_36, x_35);
if (lean::is_scalar(x_42)) {
 x_44 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_44 = x_42;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_37);
lean::cnstr_set(x_44, 2, x_38);
lean::cnstr_set(x_44, 3, x_39);
lean::cnstr_set(x_44, 4, x_40);
lean::cnstr_set(x_44, 5, x_41);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_17);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_18);
if (x_46 == 0)
{
return x_18;
}
else
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_18, 0);
x_48 = lean::cnstr_get(x_18, 1);
lean::inc(x_48);
lean::inc(x_47);
lean::dec(x_18);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_50 = lean::cnstr_get(x_6, 0);
x_51 = lean::cnstr_get(x_6, 1);
x_52 = lean::cnstr_get(x_6, 2);
x_53 = lean::cnstr_get(x_6, 3);
x_54 = lean::cnstr_get(x_6, 4);
x_55 = lean::cnstr_get(x_6, 5);
lean::inc(x_55);
lean::inc(x_54);
lean::inc(x_53);
lean::inc(x_52);
lean::inc(x_51);
lean::inc(x_50);
lean::dec(x_6);
x_56 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_57 = 1;
x_58 = l___private_init_lean_elaborator_command_1__addScopes___main(x_56, x_57, x_11, x_55);
lean::dec(x_55);
x_59 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_59, 0, x_50);
lean::cnstr_set(x_59, 1, x_51);
lean::cnstr_set(x_59, 2, x_52);
lean::cnstr_set(x_59, 3, x_53);
lean::cnstr_set(x_59, 4, x_54);
lean::cnstr_set(x_59, 5, x_58);
x_60 = lean::box(0);
lean::cnstr_set(x_3, 1, x_59);
lean::cnstr_set(x_3, 0, x_60);
x_61 = l_Lean_Elab_getNamespace___rarg(x_3);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_61, 0);
lean::inc(x_63);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_64 = x_61;
} else {
 lean::dec_ref(x_61);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_62, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_62, 1);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_62, 2);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_62, 3);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_62, 4);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_62, 5);
lean::inc(x_70);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 lean::cnstr_release(x_62, 2);
 lean::cnstr_release(x_62, 3);
 lean::cnstr_release(x_62, 4);
 lean::cnstr_release(x_62, 5);
 x_71 = x_62;
} else {
 lean::dec_ref(x_62);
 x_71 = lean::box(0);
}
x_72 = l_Lean_registerNamespace(x_65, x_63);
if (lean::is_scalar(x_71)) {
 x_73 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_73 = x_71;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_66);
lean::cnstr_set(x_73, 2, x_67);
lean::cnstr_set(x_73, 3, x_68);
lean::cnstr_set(x_73, 4, x_69);
lean::cnstr_set(x_73, 5, x_70);
if (lean::is_scalar(x_64)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_64;
}
lean::cnstr_set(x_74, 0, x_60);
lean::cnstr_set(x_74, 1, x_73);
return x_74;
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_75 = lean::cnstr_get(x_61, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_61, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_77 = x_61;
} else {
 lean::dec_ref(x_61);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_79 = lean::cnstr_get(x_1, 1);
x_80 = lean::cnstr_get(x_3, 1);
lean::inc(x_80);
lean::dec(x_3);
x_81 = lean::box(0);
x_82 = lean::mk_nat_obj(1u);
x_83 = lean_array_get(x_81, x_79, x_82);
x_84 = l_Lean_Syntax_getId___rarg(x_83);
lean::dec(x_83);
x_85 = lean::cnstr_get(x_80, 0);
lean::inc(x_85);
x_86 = lean::cnstr_get(x_80, 1);
lean::inc(x_86);
x_87 = lean::cnstr_get(x_80, 2);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_80, 3);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_80, 4);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_80, 5);
lean::inc(x_90);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 lean::cnstr_release(x_80, 1);
 lean::cnstr_release(x_80, 2);
 lean::cnstr_release(x_80, 3);
 lean::cnstr_release(x_80, 4);
 lean::cnstr_release(x_80, 5);
 x_91 = x_80;
} else {
 lean::dec_ref(x_80);
 x_91 = lean::box(0);
}
x_92 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__1;
x_93 = 1;
x_94 = l___private_init_lean_elaborator_command_1__addScopes___main(x_92, x_93, x_84, x_90);
lean::dec(x_90);
if (lean::is_scalar(x_91)) {
 x_95 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_95 = x_91;
}
lean::cnstr_set(x_95, 0, x_85);
lean::cnstr_set(x_95, 1, x_86);
lean::cnstr_set(x_95, 2, x_87);
lean::cnstr_set(x_95, 3, x_88);
lean::cnstr_set(x_95, 4, x_89);
lean::cnstr_set(x_95, 5, x_94);
x_96 = lean::box(0);
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_95);
x_98 = l_Lean_Elab_getNamespace___rarg(x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_99 = lean::cnstr_get(x_98, 1);
lean::inc(x_99);
x_100 = lean::cnstr_get(x_98, 0);
lean::inc(x_100);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_101 = x_98;
} else {
 lean::dec_ref(x_98);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_99, 0);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_99, 1);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_99, 2);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_99, 3);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_99, 4);
lean::inc(x_106);
x_107 = lean::cnstr_get(x_99, 5);
lean::inc(x_107);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 lean::cnstr_release(x_99, 2);
 lean::cnstr_release(x_99, 3);
 lean::cnstr_release(x_99, 4);
 lean::cnstr_release(x_99, 5);
 x_108 = x_99;
} else {
 lean::dec_ref(x_99);
 x_108 = lean::box(0);
}
x_109 = l_Lean_registerNamespace(x_102, x_100);
if (lean::is_scalar(x_108)) {
 x_110 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_110 = x_108;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_103);
lean::cnstr_set(x_110, 2, x_104);
lean::cnstr_set(x_110, 3, x_105);
lean::cnstr_set(x_110, 4, x_106);
lean::cnstr_set(x_110, 5, x_107);
if (lean::is_scalar(x_101)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_101;
}
lean::cnstr_set(x_111, 0, x_96);
lean::cnstr_set(x_111, 1, x_110);
return x_111;
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_112 = lean::cnstr_get(x_98, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_98, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_114 = x_98;
} else {
 lean::dec_ref(x_98);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set(x_115, 1, x_113);
return x_115;
}
}
}
}
obj* l_Lean_Elab_elabNamespace___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabNamespace(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabNamespace");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabNamespace___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabNamespace(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_namespace___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_elabSection(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = l_Lean_Elab_getNamespace___rarg(x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
x_9 = lean::box(0);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_array_get(x_9, x_4, x_10);
x_12 = l_Lean_Syntax_getOptionalIdent___rarg(x_11);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_8);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_8, 5);
x_15 = lean::box(0);
x_16 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_17 = lean::box(0);
x_18 = l_Lean_Options_empty;
x_19 = l_Lean_LocalContext_Inhabited___closed__1;
x_20 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set(x_20, 2, x_18);
lean::cnstr_set(x_20, 3, x_7);
lean::cnstr_set(x_20, 4, x_15);
lean::cnstr_set(x_20, 5, x_15);
lean::cnstr_set(x_20, 6, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_8, 5, x_21);
x_22 = lean::box(0);
lean::cnstr_set(x_5, 0, x_22);
return x_5;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_23 = lean::cnstr_get(x_8, 0);
x_24 = lean::cnstr_get(x_8, 1);
x_25 = lean::cnstr_get(x_8, 2);
x_26 = lean::cnstr_get(x_8, 3);
x_27 = lean::cnstr_get(x_8, 4);
x_28 = lean::cnstr_get(x_8, 5);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
lean::inc(x_25);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_8);
x_29 = lean::box(0);
x_30 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_31 = lean::box(0);
x_32 = l_Lean_Options_empty;
x_33 = l_Lean_LocalContext_Inhabited___closed__1;
x_34 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set(x_34, 1, x_31);
lean::cnstr_set(x_34, 2, x_32);
lean::cnstr_set(x_34, 3, x_7);
lean::cnstr_set(x_34, 4, x_29);
lean::cnstr_set(x_34, 5, x_29);
lean::cnstr_set(x_34, 6, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_28);
x_36 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_36, 0, x_23);
lean::cnstr_set(x_36, 1, x_24);
lean::cnstr_set(x_36, 2, x_25);
lean::cnstr_set(x_36, 3, x_26);
lean::cnstr_set(x_36, 4, x_27);
lean::cnstr_set(x_36, 5, x_35);
x_37 = lean::box(0);
lean::cnstr_set(x_5, 1, x_36);
lean::cnstr_set(x_5, 0, x_37);
return x_5;
}
}
else
{
obj* x_38; uint8 x_39; 
lean::dec(x_7);
x_38 = lean::cnstr_get(x_12, 0);
lean::inc(x_38);
lean::dec(x_12);
x_39 = !lean::is_exclusive(x_8);
if (x_39 == 0)
{
obj* x_40; obj* x_41; uint8 x_42; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_8, 5);
x_41 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_42 = 0;
x_43 = l___private_init_lean_elaborator_command_1__addScopes___main(x_41, x_42, x_38, x_40);
lean::dec(x_40);
lean::cnstr_set(x_8, 5, x_43);
x_44 = lean::box(0);
lean::cnstr_set(x_5, 0, x_44);
return x_5;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; 
x_45 = lean::cnstr_get(x_8, 0);
x_46 = lean::cnstr_get(x_8, 1);
x_47 = lean::cnstr_get(x_8, 2);
x_48 = lean::cnstr_get(x_8, 3);
x_49 = lean::cnstr_get(x_8, 4);
x_50 = lean::cnstr_get(x_8, 5);
lean::inc(x_50);
lean::inc(x_49);
lean::inc(x_48);
lean::inc(x_47);
lean::inc(x_46);
lean::inc(x_45);
lean::dec(x_8);
x_51 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_52 = 0;
x_53 = l___private_init_lean_elaborator_command_1__addScopes___main(x_51, x_52, x_38, x_50);
lean::dec(x_50);
x_54 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_54, 0, x_45);
lean::cnstr_set(x_54, 1, x_46);
lean::cnstr_set(x_54, 2, x_47);
lean::cnstr_set(x_54, 3, x_48);
lean::cnstr_set(x_54, 4, x_49);
lean::cnstr_set(x_54, 5, x_53);
x_55 = lean::box(0);
lean::cnstr_set(x_5, 1, x_54);
lean::cnstr_set(x_5, 0, x_55);
return x_5;
}
}
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_56 = lean::cnstr_get(x_5, 0);
x_57 = lean::cnstr_get(x_5, 1);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_5);
x_58 = lean::box(0);
x_59 = lean::mk_nat_obj(1u);
x_60 = lean_array_get(x_58, x_4, x_59);
x_61 = l_Lean_Syntax_getOptionalIdent___rarg(x_60);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_62 = lean::cnstr_get(x_57, 0);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_57, 1);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_57, 2);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_57, 3);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_57, 4);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_57, 5);
lean::inc(x_67);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 lean::cnstr_release(x_57, 2);
 lean::cnstr_release(x_57, 3);
 lean::cnstr_release(x_57, 4);
 lean::cnstr_release(x_57, 5);
 x_68 = x_57;
} else {
 lean::dec_ref(x_57);
 x_68 = lean::box(0);
}
x_69 = lean::box(0);
x_70 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_71 = lean::box(0);
x_72 = l_Lean_Options_empty;
x_73 = l_Lean_LocalContext_Inhabited___closed__1;
x_74 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set(x_74, 1, x_71);
lean::cnstr_set(x_74, 2, x_72);
lean::cnstr_set(x_74, 3, x_56);
lean::cnstr_set(x_74, 4, x_69);
lean::cnstr_set(x_74, 5, x_69);
lean::cnstr_set(x_74, 6, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_67);
if (lean::is_scalar(x_68)) {
 x_76 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_76 = x_68;
}
lean::cnstr_set(x_76, 0, x_62);
lean::cnstr_set(x_76, 1, x_63);
lean::cnstr_set(x_76, 2, x_64);
lean::cnstr_set(x_76, 3, x_65);
lean::cnstr_set(x_76, 4, x_66);
lean::cnstr_set(x_76, 5, x_75);
x_77 = lean::box(0);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; uint8 x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_56);
x_79 = lean::cnstr_get(x_61, 0);
lean::inc(x_79);
lean::dec(x_61);
x_80 = lean::cnstr_get(x_57, 0);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_57, 1);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_57, 2);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_57, 3);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_57, 4);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_57, 5);
lean::inc(x_85);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 lean::cnstr_release(x_57, 2);
 lean::cnstr_release(x_57, 3);
 lean::cnstr_release(x_57, 4);
 lean::cnstr_release(x_57, 5);
 x_86 = x_57;
} else {
 lean::dec_ref(x_57);
 x_86 = lean::box(0);
}
x_87 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__1;
x_88 = 0;
x_89 = l___private_init_lean_elaborator_command_1__addScopes___main(x_87, x_88, x_79, x_85);
lean::dec(x_85);
if (lean::is_scalar(x_86)) {
 x_90 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_90 = x_86;
}
lean::cnstr_set(x_90, 0, x_80);
lean::cnstr_set(x_90, 1, x_81);
lean::cnstr_set(x_90, 2, x_82);
lean::cnstr_set(x_90, 3, x_83);
lean::cnstr_set(x_90, 4, x_84);
lean::cnstr_set(x_90, 5, x_89);
x_91 = lean::box(0);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
uint8 x_93; 
x_93 = !lean::is_exclusive(x_5);
if (x_93 == 0)
{
return x_5;
}
else
{
obj* x_94; obj* x_95; obj* x_96; 
x_94 = lean::cnstr_get(x_5, 0);
x_95 = lean::cnstr_get(x_5, 1);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_5);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_94);
lean::cnstr_set(x_96, 1, x_95);
return x_96;
}
}
}
}
obj* l_Lean_Elab_elabSection___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabSection(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabSection");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabSection___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabSection(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_section___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l___private_init_lean_elaborator_command_2__getNumEndScopes(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::mk_nat_obj(1u);
return x_2;
}
else
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = l_Lean_Name_getNumParts___main(x_3);
return x_4;
}
}
}
obj* l___private_init_lean_elaborator_command_2__getNumEndScopes___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_elaborator_command_2__getNumEndScopes(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l___private_init_lean_elaborator_command_3__checkAnonymousScope(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_3, 1);
x_5 = lean::box(0);
x_6 = lean_name_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
}
}
obj* l___private_init_lean_elaborator_command_3__checkAnonymousScope___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l___private_init_lean_elaborator_command_3__checkAnonymousScope(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l___private_init_lean_elaborator_command_4__checkEndHeader___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_2, 1);
x_9 = lean::cnstr_get(x_5, 1);
x_10 = l_Lean_Name_eqStr(x_9, x_7);
if (x_10 == 0)
{
uint8 x_11; 
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
uint8 x_13; 
x_13 = 0;
return x_13;
}
}
}
}
obj* l___private_init_lean_elaborator_command_4__checkEndHeader___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l___private_init_lean_elaborator_command_4__checkEndHeader(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_elaborator_command_4__checkEndHeader___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l___private_init_lean_elaborator_command_4__checkEndHeader(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_Lean_Elab_elabEnd___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid 'end', insufficient scopes");
return x_1;
}
}
obj* _init_l_Lean_Elab_elabEnd___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Elab_elabEnd___closed__1;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elab_elabEnd___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid 'end', name is missing");
return x_1;
}
}
obj* _init_l_Lean_Elab_elabEnd___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Elab_elabEnd___closed__3;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Elab_elabEnd___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid 'end', name mismatch");
return x_1;
}
}
obj* _init_l_Lean_Elab_elabEnd___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Elab_elabEnd___closed__5;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Elab_elabEnd(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_5, 5);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::mk_nat_obj(0u);
x_11 = l_List_lengthAux___main___rarg(x_8, x_10);
x_12 = lean::box(0);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean_array_get(x_12, x_9, x_13);
x_15 = l_Lean_Syntax_getOptionalIdent___rarg(x_14);
lean::dec(x_14);
x_16 = l___private_init_lean_elaborator_command_2__getNumEndScopes(x_15);
x_17 = lean_nat_dec_lt(x_16, x_11);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_16);
lean::dec(x_15);
x_18 = lean_nat_sub(x_11, x_13);
lean::dec(x_11);
x_19 = l_List_drop___main___rarg(x_18, x_8);
lean::dec(x_8);
lean::cnstr_set(x_5, 5, x_19);
x_20 = l_Lean_Elab_elabEnd___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_20);
return x_3;
}
else
{
obj* x_21; 
lean::dec(x_11);
x_21 = l_List_drop___main___rarg(x_16, x_8);
lean::cnstr_set(x_5, 5, x_21);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_22; 
x_22 = l___private_init_lean_elaborator_command_3__checkAnonymousScope(x_8);
lean::dec(x_8);
if (x_22 == 0)
{
obj* x_23; 
x_23 = l_Lean_Elab_elabEnd___closed__4;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_23);
return x_3;
}
else
{
obj* x_24; 
x_24 = lean::box(0);
lean::cnstr_set(x_3, 0, x_24);
return x_3;
}
}
else
{
obj* x_25; uint8 x_26; 
x_25 = lean::cnstr_get(x_15, 0);
lean::inc(x_25);
lean::dec(x_15);
x_26 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_25, x_8);
lean::dec(x_8);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_27; 
x_27 = l_Lean_Elab_elabEnd___closed__6;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_27);
return x_3;
}
else
{
obj* x_28; 
x_28 = lean::box(0);
lean::cnstr_set(x_3, 0, x_28);
return x_3;
}
}
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; uint8 x_43; 
x_29 = lean::cnstr_get(x_5, 0);
x_30 = lean::cnstr_get(x_5, 1);
x_31 = lean::cnstr_get(x_5, 2);
x_32 = lean::cnstr_get(x_5, 3);
x_33 = lean::cnstr_get(x_5, 4);
x_34 = lean::cnstr_get(x_5, 5);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_5);
x_35 = lean::cnstr_get(x_1, 1);
x_36 = lean::mk_nat_obj(0u);
x_37 = l_List_lengthAux___main___rarg(x_34, x_36);
x_38 = lean::box(0);
x_39 = lean::mk_nat_obj(1u);
x_40 = lean_array_get(x_38, x_35, x_39);
x_41 = l_Lean_Syntax_getOptionalIdent___rarg(x_40);
lean::dec(x_40);
x_42 = l___private_init_lean_elaborator_command_2__getNumEndScopes(x_41);
x_43 = lean_nat_dec_lt(x_42, x_37);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_42);
lean::dec(x_41);
x_44 = lean_nat_sub(x_37, x_39);
lean::dec(x_37);
x_45 = l_List_drop___main___rarg(x_44, x_34);
lean::dec(x_34);
x_46 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_46, 0, x_29);
lean::cnstr_set(x_46, 1, x_30);
lean::cnstr_set(x_46, 2, x_31);
lean::cnstr_set(x_46, 3, x_32);
lean::cnstr_set(x_46, 4, x_33);
lean::cnstr_set(x_46, 5, x_45);
x_47 = l_Lean_Elab_elabEnd___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 1, x_46);
lean::cnstr_set(x_3, 0, x_47);
return x_3;
}
else
{
obj* x_48; obj* x_49; 
lean::dec(x_37);
x_48 = l_List_drop___main___rarg(x_42, x_34);
x_49 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_49, 0, x_29);
lean::cnstr_set(x_49, 1, x_30);
lean::cnstr_set(x_49, 2, x_31);
lean::cnstr_set(x_49, 3, x_32);
lean::cnstr_set(x_49, 4, x_33);
lean::cnstr_set(x_49, 5, x_48);
if (lean::obj_tag(x_41) == 0)
{
uint8 x_50; 
x_50 = l___private_init_lean_elaborator_command_3__checkAnonymousScope(x_34);
lean::dec(x_34);
if (x_50 == 0)
{
obj* x_51; 
x_51 = l_Lean_Elab_elabEnd___closed__4;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 1, x_49);
lean::cnstr_set(x_3, 0, x_51);
return x_3;
}
else
{
obj* x_52; 
x_52 = lean::box(0);
lean::cnstr_set(x_3, 1, x_49);
lean::cnstr_set(x_3, 0, x_52);
return x_3;
}
}
else
{
obj* x_53; uint8 x_54; 
x_53 = lean::cnstr_get(x_41, 0);
lean::inc(x_53);
lean::dec(x_41);
x_54 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_53, x_34);
lean::dec(x_34);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_55; 
x_55 = l_Lean_Elab_elabEnd___closed__6;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 1, x_49);
lean::cnstr_set(x_3, 0, x_55);
return x_3;
}
else
{
obj* x_56; 
x_56 = lean::box(0);
lean::cnstr_set(x_3, 1, x_49);
lean::cnstr_set(x_3, 0, x_56);
return x_3;
}
}
}
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; uint8 x_73; 
x_57 = lean::cnstr_get(x_3, 1);
lean::inc(x_57);
lean::dec(x_3);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_57, 1);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_57, 2);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_57, 3);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_57, 4);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_57, 5);
lean::inc(x_63);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 lean::cnstr_release(x_57, 2);
 lean::cnstr_release(x_57, 3);
 lean::cnstr_release(x_57, 4);
 lean::cnstr_release(x_57, 5);
 x_64 = x_57;
} else {
 lean::dec_ref(x_57);
 x_64 = lean::box(0);
}
x_65 = lean::cnstr_get(x_1, 1);
x_66 = lean::mk_nat_obj(0u);
x_67 = l_List_lengthAux___main___rarg(x_63, x_66);
x_68 = lean::box(0);
x_69 = lean::mk_nat_obj(1u);
x_70 = lean_array_get(x_68, x_65, x_69);
x_71 = l_Lean_Syntax_getOptionalIdent___rarg(x_70);
lean::dec(x_70);
x_72 = l___private_init_lean_elaborator_command_2__getNumEndScopes(x_71);
x_73 = lean_nat_dec_lt(x_72, x_67);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_72);
lean::dec(x_71);
x_74 = lean_nat_sub(x_67, x_69);
lean::dec(x_67);
x_75 = l_List_drop___main___rarg(x_74, x_63);
lean::dec(x_63);
if (lean::is_scalar(x_64)) {
 x_76 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_76 = x_64;
}
lean::cnstr_set(x_76, 0, x_58);
lean::cnstr_set(x_76, 1, x_59);
lean::cnstr_set(x_76, 2, x_60);
lean::cnstr_set(x_76, 3, x_61);
lean::cnstr_set(x_76, 4, x_62);
lean::cnstr_set(x_76, 5, x_75);
x_77 = l_Lean_Elab_elabEnd___closed__2;
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
else
{
obj* x_79; obj* x_80; 
lean::dec(x_67);
x_79 = l_List_drop___main___rarg(x_72, x_63);
if (lean::is_scalar(x_64)) {
 x_80 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_80 = x_64;
}
lean::cnstr_set(x_80, 0, x_58);
lean::cnstr_set(x_80, 1, x_59);
lean::cnstr_set(x_80, 2, x_60);
lean::cnstr_set(x_80, 3, x_61);
lean::cnstr_set(x_80, 4, x_62);
lean::cnstr_set(x_80, 5, x_79);
if (lean::obj_tag(x_71) == 0)
{
uint8 x_81; 
x_81 = l___private_init_lean_elaborator_command_3__checkAnonymousScope(x_63);
lean::dec(x_63);
if (x_81 == 0)
{
obj* x_82; obj* x_83; 
x_82 = l_Lean_Elab_elabEnd___closed__4;
x_83 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_80);
return x_83;
}
else
{
obj* x_84; obj* x_85; 
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_80);
return x_85;
}
}
else
{
obj* x_86; uint8 x_87; 
x_86 = lean::cnstr_get(x_71, 0);
lean::inc(x_86);
lean::dec(x_71);
x_87 = l___private_init_lean_elaborator_command_4__checkEndHeader___main(x_86, x_63);
lean::dec(x_63);
lean::dec(x_86);
if (x_87 == 0)
{
obj* x_88; obj* x_89; 
x_88 = l_Lean_Elab_elabEnd___closed__6;
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_80);
return x_89;
}
else
{
obj* x_90; obj* x_91; 
x_90 = lean::box(0);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_80);
return x_91;
}
}
}
}
}
}
obj* l_Lean_Elab_elabEnd___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabEnd(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabEnd");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabEnd___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabEnd(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_end___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; uint8 x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean::dec(x_10);
if (x_11 == 0)
{
uint8 x_12; 
lean::dec(x_6);
x_12 = !lean::is_exclusive(x_9);
if (x_12 == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_9, 0);
lean::dec(x_13);
lean::cnstr_set(x_9, 0, x_7);
return x_9;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::dec(x_9);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_16 = lean_array_fget(x_5, x_6);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean_nat_add(x_6, x_17);
lean::dec(x_6);
x_19 = l_Lean_Syntax_getId___rarg(x_16);
lean::inc(x_19);
x_20 = l_Lean_Name_append___main(x_2, x_19);
x_21 = l_Lean_Environment_contains(x_4, x_20);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_19);
x_22 = l_Lean_Elab_logUnknownDecl___rarg(x_16, x_20, x_8, x_9);
lean::dec(x_16);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::dec(x_24);
x_25 = lean::box(0);
lean::cnstr_set(x_22, 0, x_25);
x_6 = x_18;
x_9 = x_22;
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_6 = x_18;
x_9 = x_29;
goto _start;
}
}
else
{
uint8 x_31; 
lean::dec(x_18);
lean::dec(x_7);
x_31 = !lean::is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_22, 0);
x_33 = lean::cnstr_get(x_22, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_22);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8 x_35; 
lean::dec(x_16);
x_35 = !lean::is_exclusive(x_9);
if (x_35 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = lean::cnstr_get(x_9, 0);
lean::dec(x_36);
x_37 = l_Lean_Name_append___main(x_3, x_19);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_20);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_7);
x_40 = lean::box(0);
lean::cnstr_set(x_9, 0, x_40);
x_6 = x_18;
x_7 = x_39;
goto _start;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_9, 1);
lean::inc(x_42);
lean::dec(x_9);
x_43 = l_Lean_Name_append___main(x_3, x_19);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_20);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_7);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_42);
x_6 = x_18;
x_7 = x_45;
x_9 = x_47;
goto _start;
}
}
}
}
}
obj* l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_7 = l_Lean_addAlias(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
obj* _init_l_Lean_Elab_elabExport___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid 'export', self export");
return x_1;
}
}
obj* _init_l_Lean_Elab_elabExport___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Elab_elabExport___closed__1;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Elab_elabExport(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean::dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = lean::box(0);
lean::cnstr_set(x_9, 0, x_12);
x_13 = l_Lean_Elab_getNamespace___rarg(x_9);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = lean_name_dec_eq(x_11, x_15);
if (x_16 == 0)
{
obj* x_17; 
lean::cnstr_set(x_13, 0, x_12);
x_17 = l_Lean_Elab_getEnv___rarg(x_13);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = lean::cnstr_get(x_17, 0);
lean::cnstr_set(x_17, 0, x_12);
x_20 = lean::box(0);
x_21 = lean::mk_nat_obj(3u);
x_22 = lean_array_get(x_5, x_4, x_21);
x_23 = l_Lean_Syntax_getArgs___rarg(x_22);
lean::dec(x_22);
x_24 = lean::mk_nat_obj(0u);
x_25 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_11, x_15, x_19, x_23, x_24, x_20, x_2, x_17);
lean::dec(x_23);
lean::dec(x_19);
lean::dec(x_15);
lean::dec(x_11);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; uint8 x_28; 
x_27 = lean::cnstr_get(x_25, 1);
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_25, 0);
x_30 = lean::cnstr_get(x_27, 0);
x_31 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_30, x_29);
lean::cnstr_set(x_27, 0, x_31);
lean::cnstr_set(x_25, 0, x_12);
return x_25;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_32 = lean::cnstr_get(x_25, 0);
x_33 = lean::cnstr_get(x_27, 0);
x_34 = lean::cnstr_get(x_27, 1);
x_35 = lean::cnstr_get(x_27, 2);
x_36 = lean::cnstr_get(x_27, 3);
x_37 = lean::cnstr_get(x_27, 4);
x_38 = lean::cnstr_get(x_27, 5);
lean::inc(x_38);
lean::inc(x_37);
lean::inc(x_36);
lean::inc(x_35);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_27);
x_39 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_33, x_32);
x_40 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_34);
lean::cnstr_set(x_40, 2, x_35);
lean::cnstr_set(x_40, 3, x_36);
lean::cnstr_set(x_40, 4, x_37);
lean::cnstr_set(x_40, 5, x_38);
lean::cnstr_set(x_25, 1, x_40);
lean::cnstr_set(x_25, 0, x_12);
return x_25;
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_41 = lean::cnstr_get(x_25, 1);
x_42 = lean::cnstr_get(x_25, 0);
lean::inc(x_41);
lean::inc(x_42);
lean::dec(x_25);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_41, 2);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_41, 3);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_41, 4);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_41, 5);
lean::inc(x_48);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 lean::cnstr_release(x_41, 2);
 lean::cnstr_release(x_41, 3);
 lean::cnstr_release(x_41, 4);
 lean::cnstr_release(x_41, 5);
 x_49 = x_41;
} else {
 lean::dec_ref(x_41);
 x_49 = lean::box(0);
}
x_50 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_43, x_42);
if (lean::is_scalar(x_49)) {
 x_51 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_51 = x_49;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_45);
lean::cnstr_set(x_51, 3, x_46);
lean::cnstr_set(x_51, 4, x_47);
lean::cnstr_set(x_51, 5, x_48);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_12);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8 x_53; 
x_53 = !lean::is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::cnstr_get(x_25, 0);
x_55 = lean::cnstr_get(x_25, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_25);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_57 = lean::cnstr_get(x_17, 0);
x_58 = lean::cnstr_get(x_17, 1);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_17);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_12);
lean::cnstr_set(x_59, 1, x_58);
x_60 = lean::box(0);
x_61 = lean::mk_nat_obj(3u);
x_62 = lean_array_get(x_5, x_4, x_61);
x_63 = l_Lean_Syntax_getArgs___rarg(x_62);
lean::dec(x_62);
x_64 = lean::mk_nat_obj(0u);
x_65 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_11, x_15, x_57, x_63, x_64, x_60, x_2, x_59);
lean::dec(x_63);
lean::dec(x_57);
lean::dec(x_15);
lean::dec(x_11);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_66 = lean::cnstr_get(x_65, 1);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_65, 0);
lean::inc(x_67);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_68 = x_65;
} else {
 lean::dec_ref(x_65);
 x_68 = lean::box(0);
}
x_69 = lean::cnstr_get(x_66, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_66, 1);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_66, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_66, 3);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_66, 4);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_66, 5);
lean::inc(x_74);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 lean::cnstr_release(x_66, 1);
 lean::cnstr_release(x_66, 2);
 lean::cnstr_release(x_66, 3);
 lean::cnstr_release(x_66, 4);
 lean::cnstr_release(x_66, 5);
 x_75 = x_66;
} else {
 lean::dec_ref(x_66);
 x_75 = lean::box(0);
}
x_76 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_69, x_67);
if (lean::is_scalar(x_75)) {
 x_77 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_77 = x_75;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_70);
lean::cnstr_set(x_77, 2, x_71);
lean::cnstr_set(x_77, 3, x_72);
lean::cnstr_set(x_77, 4, x_73);
lean::cnstr_set(x_77, 5, x_74);
if (lean::is_scalar(x_68)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_68;
}
lean::cnstr_set(x_78, 0, x_12);
lean::cnstr_set(x_78, 1, x_77);
return x_78;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_79 = lean::cnstr_get(x_65, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_65, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_81 = x_65;
} else {
 lean::dec_ref(x_65);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
lean::cnstr_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8 x_83; 
lean::dec(x_15);
lean::dec(x_11);
x_83 = !lean::is_exclusive(x_17);
if (x_83 == 0)
{
return x_17;
}
else
{
obj* x_84; obj* x_85; obj* x_86; 
x_84 = lean::cnstr_get(x_17, 0);
x_85 = lean::cnstr_get(x_17, 1);
lean::inc(x_85);
lean::inc(x_84);
lean::dec(x_17);
x_86 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
obj* x_87; 
lean::dec(x_15);
lean::dec(x_11);
x_87 = l_Lean_Elab_elabExport___closed__2;
lean::cnstr_set_tag(x_13, 1);
lean::cnstr_set(x_13, 0, x_87);
return x_13;
}
}
else
{
obj* x_88; obj* x_89; uint8 x_90; 
x_88 = lean::cnstr_get(x_13, 0);
x_89 = lean::cnstr_get(x_13, 1);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_13);
x_90 = lean_name_dec_eq(x_11, x_88);
if (x_90 == 0)
{
obj* x_91; obj* x_92; 
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_12);
lean::cnstr_set(x_91, 1, x_89);
x_92 = l_Lean_Elab_getEnv___rarg(x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_95 = x_92;
} else {
 lean::dec_ref(x_92);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_12);
lean::cnstr_set(x_96, 1, x_94);
x_97 = lean::box(0);
x_98 = lean::mk_nat_obj(3u);
x_99 = lean_array_get(x_5, x_4, x_98);
x_100 = l_Lean_Syntax_getArgs___rarg(x_99);
lean::dec(x_99);
x_101 = lean::mk_nat_obj(0u);
x_102 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_11, x_88, x_93, x_100, x_101, x_97, x_2, x_96);
lean::dec(x_100);
lean::dec(x_93);
lean::dec(x_88);
lean::dec(x_11);
if (lean::obj_tag(x_102) == 0)
{
obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_103 = lean::cnstr_get(x_102, 1);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_102, 0);
lean::inc(x_104);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 lean::cnstr_release(x_102, 1);
 x_105 = x_102;
} else {
 lean::dec_ref(x_102);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_103, 0);
lean::inc(x_106);
x_107 = lean::cnstr_get(x_103, 1);
lean::inc(x_107);
x_108 = lean::cnstr_get(x_103, 2);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_103, 3);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_103, 4);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_103, 5);
lean::inc(x_111);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 lean::cnstr_release(x_103, 1);
 lean::cnstr_release(x_103, 2);
 lean::cnstr_release(x_103, 3);
 lean::cnstr_release(x_103, 4);
 lean::cnstr_release(x_103, 5);
 x_112 = x_103;
} else {
 lean::dec_ref(x_103);
 x_112 = lean::box(0);
}
x_113 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_106, x_104);
if (lean::is_scalar(x_112)) {
 x_114 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_114 = x_112;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_107);
lean::cnstr_set(x_114, 2, x_108);
lean::cnstr_set(x_114, 3, x_109);
lean::cnstr_set(x_114, 4, x_110);
lean::cnstr_set(x_114, 5, x_111);
if (lean::is_scalar(x_105)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_105;
}
lean::cnstr_set(x_115, 0, x_12);
lean::cnstr_set(x_115, 1, x_114);
return x_115;
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_116 = lean::cnstr_get(x_102, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_102, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 lean::cnstr_release(x_102, 1);
 x_118 = x_102;
} else {
 lean::dec_ref(x_102);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_116);
lean::cnstr_set(x_119, 1, x_117);
return x_119;
}
}
else
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
lean::dec(x_88);
lean::dec(x_11);
x_120 = lean::cnstr_get(x_92, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_92, 1);
lean::inc(x_121);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_122 = x_92;
} else {
 lean::dec_ref(x_92);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_120);
lean::cnstr_set(x_123, 1, x_121);
return x_123;
}
}
else
{
obj* x_124; obj* x_125; 
lean::dec(x_88);
lean::dec(x_11);
x_124 = l_Lean_Elab_elabExport___closed__2;
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_89);
return x_125;
}
}
}
else
{
uint8 x_126; 
lean::dec(x_11);
x_126 = !lean::is_exclusive(x_13);
if (x_126 == 0)
{
return x_13;
}
else
{
obj* x_127; obj* x_128; obj* x_129; 
x_127 = lean::cnstr_get(x_13, 0);
x_128 = lean::cnstr_get(x_13, 1);
lean::inc(x_128);
lean::inc(x_127);
lean::dec(x_13);
x_129 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_130 = lean::cnstr_get(x_9, 0);
x_131 = lean::cnstr_get(x_9, 1);
lean::inc(x_131);
lean::inc(x_130);
lean::dec(x_9);
x_132 = lean::box(0);
x_133 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_131);
x_134 = l_Lean_Elab_getNamespace___rarg(x_133);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; obj* x_136; obj* x_137; uint8 x_138; 
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
x_136 = lean::cnstr_get(x_134, 1);
lean::inc(x_136);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_137 = x_134;
} else {
 lean::dec_ref(x_134);
 x_137 = lean::box(0);
}
x_138 = lean_name_dec_eq(x_130, x_135);
if (x_138 == 0)
{
obj* x_139; obj* x_140; 
if (lean::is_scalar(x_137)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_137;
}
lean::cnstr_set(x_139, 0, x_132);
lean::cnstr_set(x_139, 1, x_136);
x_140 = l_Lean_Elab_getEnv___rarg(x_139);
if (lean::obj_tag(x_140) == 0)
{
obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_141 = lean::cnstr_get(x_140, 0);
lean::inc(x_141);
x_142 = lean::cnstr_get(x_140, 1);
lean::inc(x_142);
if (lean::is_exclusive(x_140)) {
 lean::cnstr_release(x_140, 0);
 lean::cnstr_release(x_140, 1);
 x_143 = x_140;
} else {
 lean::dec_ref(x_140);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_132);
lean::cnstr_set(x_144, 1, x_142);
x_145 = lean::box(0);
x_146 = lean::mk_nat_obj(3u);
x_147 = lean_array_get(x_5, x_4, x_146);
x_148 = l_Lean_Syntax_getArgs___rarg(x_147);
lean::dec(x_147);
x_149 = lean::mk_nat_obj(0u);
x_150 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_4, x_130, x_135, x_141, x_148, x_149, x_145, x_2, x_144);
lean::dec(x_148);
lean::dec(x_141);
lean::dec(x_135);
lean::dec(x_130);
if (lean::obj_tag(x_150) == 0)
{
obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
x_151 = lean::cnstr_get(x_150, 1);
lean::inc(x_151);
x_152 = lean::cnstr_get(x_150, 0);
lean::inc(x_152);
if (lean::is_exclusive(x_150)) {
 lean::cnstr_release(x_150, 0);
 lean::cnstr_release(x_150, 1);
 x_153 = x_150;
} else {
 lean::dec_ref(x_150);
 x_153 = lean::box(0);
}
x_154 = lean::cnstr_get(x_151, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_151, 1);
lean::inc(x_155);
x_156 = lean::cnstr_get(x_151, 2);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_151, 3);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_151, 4);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_151, 5);
lean::inc(x_159);
if (lean::is_exclusive(x_151)) {
 lean::cnstr_release(x_151, 0);
 lean::cnstr_release(x_151, 1);
 lean::cnstr_release(x_151, 2);
 lean::cnstr_release(x_151, 3);
 lean::cnstr_release(x_151, 4);
 lean::cnstr_release(x_151, 5);
 x_160 = x_151;
} else {
 lean::dec_ref(x_151);
 x_160 = lean::box(0);
}
x_161 = l_List_foldl___main___at_Lean_Elab_elabExport___spec__2(x_154, x_152);
if (lean::is_scalar(x_160)) {
 x_162 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_162 = x_160;
}
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_155);
lean::cnstr_set(x_162, 2, x_156);
lean::cnstr_set(x_162, 3, x_157);
lean::cnstr_set(x_162, 4, x_158);
lean::cnstr_set(x_162, 5, x_159);
if (lean::is_scalar(x_153)) {
 x_163 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_163 = x_153;
}
lean::cnstr_set(x_163, 0, x_132);
lean::cnstr_set(x_163, 1, x_162);
return x_163;
}
else
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
x_164 = lean::cnstr_get(x_150, 0);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_150, 1);
lean::inc(x_165);
if (lean::is_exclusive(x_150)) {
 lean::cnstr_release(x_150, 0);
 lean::cnstr_release(x_150, 1);
 x_166 = x_150;
} else {
 lean::dec_ref(x_150);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_164);
lean::cnstr_set(x_167, 1, x_165);
return x_167;
}
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
lean::dec(x_135);
lean::dec(x_130);
x_168 = lean::cnstr_get(x_140, 0);
lean::inc(x_168);
x_169 = lean::cnstr_get(x_140, 1);
lean::inc(x_169);
if (lean::is_exclusive(x_140)) {
 lean::cnstr_release(x_140, 0);
 lean::cnstr_release(x_140, 1);
 x_170 = x_140;
} else {
 lean::dec_ref(x_140);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
lean::cnstr_set(x_171, 1, x_169);
return x_171;
}
}
else
{
obj* x_172; obj* x_173; 
lean::dec(x_135);
lean::dec(x_130);
x_172 = l_Lean_Elab_elabExport___closed__2;
if (lean::is_scalar(x_137)) {
 x_173 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_173 = x_137;
 lean::cnstr_set_tag(x_173, 1);
}
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_136);
return x_173;
}
}
else
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_130);
x_174 = lean::cnstr_get(x_134, 0);
lean::inc(x_174);
x_175 = lean::cnstr_get(x_134, 1);
lean::inc(x_175);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_176 = x_134;
} else {
 lean::dec_ref(x_134);
 x_176 = lean::box(0);
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_174);
lean::cnstr_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
uint8 x_178; 
x_178 = !lean::is_exclusive(x_9);
if (x_178 == 0)
{
return x_9;
}
else
{
obj* x_179; obj* x_180; obj* x_181; 
x_179 = lean::cnstr_get(x_9, 0);
x_180 = lean::cnstr_get(x_9, 1);
lean::inc(x_180);
lean::inc(x_179);
lean::dec(x_9);
x_181 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_181, 0, x_179);
lean::cnstr_set(x_181, 1, x_180);
return x_181;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l_Array_miterateAux___main___at_Lean_Elab_elabExport___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean::dec(x_8);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_10;
}
}
obj* l_Lean_Elab_elabExport___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabExport(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabExport");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabExport___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabExport(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_export___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_modifyScope(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
x_7 = lean::cnstr_get(x_5, 5);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::dec(x_1);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_5, 5);
lean::dec(x_9);
x_10 = lean::box(0);
lean::cnstr_set(x_3, 0, x_10);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
x_13 = lean::cnstr_get(x_5, 2);
x_14 = lean::cnstr_get(x_5, 3);
x_15 = lean::cnstr_get(x_5, 4);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_12);
lean::cnstr_set(x_16, 2, x_13);
lean::cnstr_set(x_16, 3, x_14);
lean::cnstr_set(x_16, 4, x_15);
lean::cnstr_set(x_16, 5, x_7);
x_17 = lean::box(0);
lean::cnstr_set(x_3, 1, x_16);
lean::cnstr_set(x_3, 0, x_17);
return x_3;
}
}
else
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_5);
if (x_18 == 0)
{
obj* x_19; uint8 x_20; 
x_19 = lean::cnstr_get(x_5, 5);
lean::dec(x_19);
x_20 = !lean::is_exclusive(x_7);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_7, 0);
x_22 = lean::apply_1(x_1, x_21);
lean::cnstr_set(x_7, 0, x_22);
x_23 = lean::box(0);
lean::cnstr_set(x_3, 0, x_23);
return x_3;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_7, 0);
x_25 = lean::cnstr_get(x_7, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_7);
x_26 = lean::apply_1(x_1, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
lean::cnstr_set(x_5, 5, x_27);
x_28 = lean::box(0);
lean::cnstr_set(x_3, 0, x_28);
return x_3;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_29 = lean::cnstr_get(x_5, 0);
x_30 = lean::cnstr_get(x_5, 1);
x_31 = lean::cnstr_get(x_5, 2);
x_32 = lean::cnstr_get(x_5, 3);
x_33 = lean::cnstr_get(x_5, 4);
lean::inc(x_33);
lean::inc(x_32);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_5);
x_34 = lean::cnstr_get(x_7, 0);
lean::inc(x_34);
x_35 = lean::cnstr_get(x_7, 1);
lean::inc(x_35);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_36 = x_7;
} else {
 lean::dec_ref(x_7);
 x_36 = lean::box(0);
}
x_37 = lean::apply_1(x_1, x_34);
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_35);
x_39 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set(x_39, 1, x_30);
lean::cnstr_set(x_39, 2, x_31);
lean::cnstr_set(x_39, 3, x_32);
lean::cnstr_set(x_39, 4, x_33);
lean::cnstr_set(x_39, 5, x_38);
x_40 = lean::box(0);
lean::cnstr_set(x_3, 1, x_39);
lean::cnstr_set(x_3, 0, x_40);
return x_3;
}
}
}
else
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_3, 1);
lean::inc(x_41);
lean::dec(x_3);
x_42 = lean::cnstr_get(x_41, 5);
lean::inc(x_42);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_1);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_41, 2);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_41, 3);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_41, 4);
lean::inc(x_47);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 lean::cnstr_release(x_41, 2);
 lean::cnstr_release(x_41, 3);
 lean::cnstr_release(x_41, 4);
 lean::cnstr_release(x_41, 5);
 x_48 = x_41;
} else {
 lean::dec_ref(x_41);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_43);
lean::cnstr_set(x_49, 1, x_44);
lean::cnstr_set(x_49, 2, x_45);
lean::cnstr_set(x_49, 3, x_46);
lean::cnstr_set(x_49, 4, x_47);
lean::cnstr_set(x_49, 5, x_42);
x_50 = lean::box(0);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_52 = lean::cnstr_get(x_41, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_41, 1);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_41, 2);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_41, 3);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_41, 4);
lean::inc(x_56);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 lean::cnstr_release(x_41, 2);
 lean::cnstr_release(x_41, 3);
 lean::cnstr_release(x_41, 4);
 lean::cnstr_release(x_41, 5);
 x_57 = x_41;
} else {
 lean::dec_ref(x_41);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_42, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_42, 1);
lean::inc(x_59);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_60 = x_42;
} else {
 lean::dec_ref(x_42);
 x_60 = lean::box(0);
}
x_61 = lean::apply_1(x_1, x_58);
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_59);
if (lean::is_scalar(x_57)) {
 x_63 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_63 = x_57;
}
lean::cnstr_set(x_63, 0, x_52);
lean::cnstr_set(x_63, 1, x_53);
lean::cnstr_set(x_63, 2, x_54);
lean::cnstr_set(x_63, 3, x_55);
lean::cnstr_set(x_63, 4, x_56);
lean::cnstr_set(x_63, 5, x_62);
x_64 = lean::box(0);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_63);
return x_65;
}
}
}
}
obj* l_Lean_Elab_modifyScope___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_modifyScope(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
x_7 = lean::cnstr_get(x_5, 5);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::dec(x_1);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_5, 5);
lean::dec(x_9);
x_10 = lean::box(0);
lean::cnstr_set(x_3, 0, x_10);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
x_13 = lean::cnstr_get(x_5, 2);
x_14 = lean::cnstr_get(x_5, 3);
x_15 = lean::cnstr_get(x_5, 4);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_12);
lean::cnstr_set(x_16, 2, x_13);
lean::cnstr_set(x_16, 3, x_14);
lean::cnstr_set(x_16, 4, x_15);
lean::cnstr_set(x_16, 5, x_7);
x_17 = lean::box(0);
lean::cnstr_set(x_3, 1, x_16);
lean::cnstr_set(x_3, 0, x_17);
return x_3;
}
}
else
{
obj* x_18; uint8 x_19; 
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
x_19 = !lean::is_exclusive(x_5);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = lean::cnstr_get(x_5, 5);
lean::dec(x_20);
x_21 = !lean::is_exclusive(x_7);
if (x_21 == 0)
{
obj* x_22; obj* x_23; uint8 x_24; 
x_22 = lean::cnstr_get(x_7, 1);
x_23 = lean::cnstr_get(x_7, 0);
lean::dec(x_23);
x_24 = !lean::is_exclusive(x_18);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = lean::cnstr_get(x_18, 4);
lean::cnstr_set(x_7, 1, x_25);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_18, 4, x_7);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_18);
lean::cnstr_set(x_26, 1, x_22);
lean::cnstr_set(x_5, 5, x_26);
x_27 = lean::box(0);
lean::cnstr_set(x_3, 0, x_27);
return x_3;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_28 = lean::cnstr_get(x_18, 0);
x_29 = lean::cnstr_get(x_18, 1);
x_30 = lean::cnstr_get(x_18, 2);
x_31 = lean::cnstr_get(x_18, 3);
x_32 = lean::cnstr_get(x_18, 4);
x_33 = lean::cnstr_get(x_18, 5);
x_34 = lean::cnstr_get(x_18, 6);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_18);
lean::cnstr_set(x_7, 1, x_32);
lean::cnstr_set(x_7, 0, x_1);
x_35 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_29);
lean::cnstr_set(x_35, 2, x_30);
lean::cnstr_set(x_35, 3, x_31);
lean::cnstr_set(x_35, 4, x_7);
lean::cnstr_set(x_35, 5, x_33);
lean::cnstr_set(x_35, 6, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_22);
lean::cnstr_set(x_5, 5, x_36);
x_37 = lean::box(0);
lean::cnstr_set(x_3, 0, x_37);
return x_3;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_38 = lean::cnstr_get(x_7, 1);
lean::inc(x_38);
lean::dec(x_7);
x_39 = lean::cnstr_get(x_18, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_18, 1);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_18, 2);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_18, 3);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_18, 4);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_18, 5);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_18, 6);
lean::inc(x_45);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 lean::cnstr_release(x_18, 2);
 lean::cnstr_release(x_18, 3);
 lean::cnstr_release(x_18, 4);
 lean::cnstr_release(x_18, 5);
 lean::cnstr_release(x_18, 6);
 x_46 = x_18;
} else {
 lean::dec_ref(x_18);
 x_46 = lean::box(0);
}
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_1);
lean::cnstr_set(x_47, 1, x_43);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_39);
lean::cnstr_set(x_48, 1, x_40);
lean::cnstr_set(x_48, 2, x_41);
lean::cnstr_set(x_48, 3, x_42);
lean::cnstr_set(x_48, 4, x_47);
lean::cnstr_set(x_48, 5, x_44);
lean::cnstr_set(x_48, 6, x_45);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_38);
lean::cnstr_set(x_5, 5, x_49);
x_50 = lean::box(0);
lean::cnstr_set(x_3, 0, x_50);
return x_3;
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_51 = lean::cnstr_get(x_5, 0);
x_52 = lean::cnstr_get(x_5, 1);
x_53 = lean::cnstr_get(x_5, 2);
x_54 = lean::cnstr_get(x_5, 3);
x_55 = lean::cnstr_get(x_5, 4);
lean::inc(x_55);
lean::inc(x_54);
lean::inc(x_53);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_5);
x_56 = lean::cnstr_get(x_7, 1);
lean::inc(x_56);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_57 = x_7;
} else {
 lean::dec_ref(x_7);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_18, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_18, 1);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_18, 2);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_18, 3);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_18, 4);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_18, 5);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_18, 6);
lean::inc(x_64);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 lean::cnstr_release(x_18, 2);
 lean::cnstr_release(x_18, 3);
 lean::cnstr_release(x_18, 4);
 lean::cnstr_release(x_18, 5);
 lean::cnstr_release(x_18, 6);
 x_65 = x_18;
} else {
 lean::dec_ref(x_18);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_57;
}
lean::cnstr_set(x_66, 0, x_1);
lean::cnstr_set(x_66, 1, x_62);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_58);
lean::cnstr_set(x_67, 1, x_59);
lean::cnstr_set(x_67, 2, x_60);
lean::cnstr_set(x_67, 3, x_61);
lean::cnstr_set(x_67, 4, x_66);
lean::cnstr_set(x_67, 5, x_63);
lean::cnstr_set(x_67, 6, x_64);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_56);
x_69 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_69, 0, x_51);
lean::cnstr_set(x_69, 1, x_52);
lean::cnstr_set(x_69, 2, x_53);
lean::cnstr_set(x_69, 3, x_54);
lean::cnstr_set(x_69, 4, x_55);
lean::cnstr_set(x_69, 5, x_68);
x_70 = lean::box(0);
lean::cnstr_set(x_3, 1, x_69);
lean::cnstr_set(x_3, 0, x_70);
return x_3;
}
}
}
else
{
obj* x_71; obj* x_72; 
x_71 = lean::cnstr_get(x_3, 1);
lean::inc(x_71);
lean::dec(x_3);
x_72 = lean::cnstr_get(x_71, 5);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_1);
x_73 = lean::cnstr_get(x_71, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_71, 2);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_71, 3);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_71, 4);
lean::inc(x_77);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 lean::cnstr_release(x_71, 2);
 lean::cnstr_release(x_71, 3);
 lean::cnstr_release(x_71, 4);
 lean::cnstr_release(x_71, 5);
 x_78 = x_71;
} else {
 lean::dec_ref(x_71);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_73);
lean::cnstr_set(x_79, 1, x_74);
lean::cnstr_set(x_79, 2, x_75);
lean::cnstr_set(x_79, 3, x_76);
lean::cnstr_set(x_79, 4, x_77);
lean::cnstr_set(x_79, 5, x_72);
x_80 = lean::box(0);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_79);
return x_81;
}
else
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_82 = lean::cnstr_get(x_72, 0);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_71, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_71, 1);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_71, 2);
lean::inc(x_85);
x_86 = lean::cnstr_get(x_71, 3);
lean::inc(x_86);
x_87 = lean::cnstr_get(x_71, 4);
lean::inc(x_87);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 lean::cnstr_release(x_71, 2);
 lean::cnstr_release(x_71, 3);
 lean::cnstr_release(x_71, 4);
 lean::cnstr_release(x_71, 5);
 x_88 = x_71;
} else {
 lean::dec_ref(x_71);
 x_88 = lean::box(0);
}
x_89 = lean::cnstr_get(x_72, 1);
lean::inc(x_89);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_90 = x_72;
} else {
 lean::dec_ref(x_72);
 x_90 = lean::box(0);
}
x_91 = lean::cnstr_get(x_82, 0);
lean::inc(x_91);
x_92 = lean::cnstr_get(x_82, 1);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_82, 2);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_82, 3);
lean::inc(x_94);
x_95 = lean::cnstr_get(x_82, 4);
lean::inc(x_95);
x_96 = lean::cnstr_get(x_82, 5);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_82, 6);
lean::inc(x_97);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 lean::cnstr_release(x_82, 2);
 lean::cnstr_release(x_82, 3);
 lean::cnstr_release(x_82, 4);
 lean::cnstr_release(x_82, 5);
 lean::cnstr_release(x_82, 6);
 x_98 = x_82;
} else {
 lean::dec_ref(x_82);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_90;
}
lean::cnstr_set(x_99, 0, x_1);
lean::cnstr_set(x_99, 1, x_95);
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_91);
lean::cnstr_set(x_100, 1, x_92);
lean::cnstr_set(x_100, 2, x_93);
lean::cnstr_set(x_100, 3, x_94);
lean::cnstr_set(x_100, 4, x_99);
lean::cnstr_set(x_100, 5, x_96);
lean::cnstr_set(x_100, 6, x_97);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_89);
if (lean::is_scalar(x_88)) {
 x_102 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_102 = x_88;
}
lean::cnstr_set(x_102, 0, x_83);
lean::cnstr_set(x_102, 1, x_84);
lean::cnstr_set(x_102, 2, x_85);
lean::cnstr_set(x_102, 3, x_86);
lean::cnstr_set(x_102, 4, x_87);
lean::cnstr_set(x_102, 5, x_101);
x_103 = lean::box(0);
x_104 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_102);
return x_104;
}
}
}
}
obj* l_Lean_Elab_addOpenDecl(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Elab_addOpenDecl___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_addOpenDecl(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_3);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
lean::cnstr_set(x_6, 0, x_4);
return x_6;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_4);
x_13 = lean_array_fget(x_2, x_3);
x_14 = l_Lean_Syntax_getId___rarg(x_13);
lean::dec(x_13);
x_15 = l_Lean_Elab_resolveNamespace(x_14, x_5, x_6);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_15, 0);
x_18 = lean::box(0);
lean::cnstr_set(x_15, 0, x_18);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_20, x_5, x_15);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_21, 0);
lean::cnstr_set(x_21, 0, x_18);
x_24 = lean_nat_add(x_3, x_1);
lean::dec(x_3);
x_3 = x_24;
x_4 = x_23;
x_6 = x_21;
goto _start;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_21, 0);
x_27 = lean::cnstr_get(x_21, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_21);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_18);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean_nat_add(x_3, x_1);
lean::dec(x_3);
x_3 = x_29;
x_4 = x_26;
x_6 = x_28;
goto _start;
}
}
else
{
uint8 x_31; 
lean::dec(x_3);
x_31 = !lean::is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_21, 0);
x_33 = lean::cnstr_get(x_21, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_21);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_15, 0);
x_36 = lean::cnstr_get(x_15, 1);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_15);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_36);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_35);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_40, x_5, x_38);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_41, 1);
lean::inc(x_43);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_44 = x_41;
} else {
 lean::dec_ref(x_41);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_37);
lean::cnstr_set(x_45, 1, x_43);
x_46 = lean_nat_add(x_3, x_1);
lean::dec(x_3);
x_3 = x_46;
x_4 = x_42;
x_6 = x_45;
goto _start;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_3);
x_48 = lean::cnstr_get(x_41, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_41, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_50 = x_41;
} else {
 lean::dec_ref(x_41);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8 x_52; 
lean::dec(x_3);
x_52 = !lean::is_exclusive(x_15);
if (x_52 == 0)
{
return x_15;
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_15, 0);
x_54 = lean::cnstr_get(x_15, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_15);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
obj* l_Lean_Elab_elabOpenSimple(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs___rarg(x_7);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::box(0);
x_11 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(x_9, x_8, x_6, x_10, x_2, x_3);
lean::dec(x_8);
return x_11;
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenSimple___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Elab_elabOpenSimple___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabOpenSimple(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_4);
x_10 = !lean::is_exclusive(x_7);
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::cnstr_get(x_7, 0);
lean::dec(x_11);
lean::cnstr_set(x_7, 0, x_5);
return x_7;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_5);
x_14 = lean_array_fget(x_3, x_4);
x_15 = l_Lean_Syntax_getId___rarg(x_14);
lean::inc(x_15);
x_16 = l_Lean_Name_append___main(x_1, x_15);
x_17 = l_Lean_Elab_getEnv___rarg(x_7);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; 
x_19 = lean::cnstr_get(x_17, 0);
x_20 = lean::box(0);
lean::cnstr_set(x_17, 0, x_20);
x_21 = l_Lean_Environment_contains(x_19, x_16);
lean::dec(x_19);
if (x_21 == 0)
{
obj* x_22; 
lean::dec(x_15);
x_22 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_16, x_6, x_17);
lean::dec(x_14);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_22, 0);
lean::cnstr_set(x_22, 0, x_20);
x_25 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_25;
x_5 = x_24;
x_7 = x_22;
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_27 = lean::cnstr_get(x_22, 0);
x_28 = lean::cnstr_get(x_22, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_22);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_20);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_30;
x_5 = x_27;
x_7 = x_29;
goto _start;
}
}
else
{
uint8 x_32; 
lean::dec(x_4);
x_32 = !lean::is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_22, 0);
x_34 = lean::cnstr_get(x_22, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_22);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_14);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_15);
lean::cnstr_set(x_36, 1, x_16);
x_37 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_36, x_6, x_17);
if (lean::obj_tag(x_37) == 0)
{
uint8 x_38; 
x_38 = !lean::is_exclusive(x_37);
if (x_38 == 0)
{
obj* x_39; obj* x_40; 
x_39 = lean::cnstr_get(x_37, 0);
lean::cnstr_set(x_37, 0, x_20);
x_40 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_40;
x_5 = x_39;
x_7 = x_37;
goto _start;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = lean::cnstr_get(x_37, 0);
x_43 = lean::cnstr_get(x_37, 1);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_37);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_20);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_45;
x_5 = x_42;
x_7 = x_44;
goto _start;
}
}
else
{
uint8 x_47; 
lean::dec(x_4);
x_47 = !lean::is_exclusive(x_37);
if (x_47 == 0)
{
return x_37;
}
else
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_37, 0);
x_49 = lean::cnstr_get(x_37, 1);
lean::inc(x_49);
lean::inc(x_48);
lean::dec(x_37);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_17, 0);
x_52 = lean::cnstr_get(x_17, 1);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_17);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = l_Lean_Environment_contains(x_51, x_16);
lean::dec(x_51);
if (x_55 == 0)
{
obj* x_56; 
lean::dec(x_15);
x_56 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_16, x_6, x_54);
lean::dec(x_14);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_59 = x_56;
} else {
 lean::dec_ref(x_56);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_53);
lean::cnstr_set(x_60, 1, x_58);
x_61 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_61;
x_5 = x_57;
x_7 = x_60;
goto _start;
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_4);
x_63 = lean::cnstr_get(x_56, 0);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_56, 1);
lean::inc(x_64);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_65 = x_56;
} else {
 lean::dec_ref(x_56);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_63);
lean::cnstr_set(x_66, 1, x_64);
return x_66;
}
}
else
{
obj* x_67; obj* x_68; 
lean::dec(x_14);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_15);
lean::cnstr_set(x_67, 1, x_16);
x_68 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_67, x_6, x_54);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_68, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_71 = x_68;
} else {
 lean::dec_ref(x_68);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_53);
lean::cnstr_set(x_72, 1, x_70);
x_73 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_73;
x_5 = x_69;
x_7 = x_72;
goto _start;
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_4);
x_75 = lean::cnstr_get(x_68, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_68, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 x_77 = x_68;
} else {
 lean::dec_ref(x_68);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
uint8 x_79; 
lean::dec(x_16);
lean::dec(x_15);
lean::dec(x_14);
lean::dec(x_4);
x_79 = !lean::is_exclusive(x_17);
if (x_79 == 0)
{
return x_17;
}
else
{
obj* x_80; obj* x_81; obj* x_82; 
x_80 = lean::cnstr_get(x_17, 0);
x_81 = lean::cnstr_get(x_17, 1);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_17);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
obj* l_Lean_Elab_elabOpenOnly(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean::dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = lean::box(0);
lean::cnstr_set(x_9, 0, x_12);
x_13 = lean::mk_nat_obj(2u);
x_14 = lean_array_get(x_5, x_4, x_13);
x_15 = l_Lean_Syntax_getArgs___rarg(x_14);
lean::dec(x_14);
x_16 = lean::mk_nat_obj(1u);
x_17 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_11, x_16, x_15, x_6, x_12, x_2, x_9);
lean::dec(x_15);
lean::dec(x_11);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_18 = lean::cnstr_get(x_9, 0);
x_19 = lean::cnstr_get(x_9, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_9);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
x_22 = lean::mk_nat_obj(2u);
x_23 = lean_array_get(x_5, x_4, x_22);
x_24 = l_Lean_Syntax_getArgs___rarg(x_23);
lean::dec(x_23);
x_25 = lean::mk_nat_obj(1u);
x_26 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_18, x_25, x_24, x_6, x_20, x_2, x_21);
lean::dec(x_24);
lean::dec(x_18);
return x_26;
}
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_9, 0);
x_29 = lean::cnstr_get(x_9, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_9);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenOnly___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_Elab_elabOpenOnly___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabOpenOnly(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; uint8 x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
uint8 x_11; 
lean::dec(x_5);
x_11 = !lean::is_exclusive(x_8);
if (x_11 == 0)
{
obj* x_12; 
x_12 = lean::cnstr_get(x_8, 0);
lean::dec(x_12);
lean::cnstr_set(x_8, 0, x_6);
return x_8;
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_15 = lean_array_fget(x_4, x_5);
x_16 = l_Lean_Syntax_getId___rarg(x_15);
lean::inc(x_16);
x_17 = l_Lean_Name_append___main(x_1, x_16);
x_18 = l_Lean_Environment_contains(x_2, x_17);
if (x_18 == 0)
{
obj* x_19; 
lean::dec(x_16);
x_19 = l_Lean_Elab_logUnknownDecl___rarg(x_15, x_17, x_7, x_8);
lean::dec(x_15);
if (lean::obj_tag(x_19) == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_19, 0);
lean::dec(x_21);
x_22 = lean::box(0);
lean::cnstr_set(x_19, 0, x_22);
x_23 = lean_nat_add(x_5, x_3);
lean::dec(x_5);
x_5 = x_23;
x_8 = x_19;
goto _start;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_19, 1);
lean::inc(x_25);
lean::dec(x_19);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = lean_nat_add(x_5, x_3);
lean::dec(x_5);
x_5 = x_28;
x_8 = x_27;
goto _start;
}
}
else
{
uint8 x_30; 
lean::dec(x_6);
lean::dec(x_5);
x_30 = !lean::is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = lean::cnstr_get(x_19, 0);
x_32 = lean::cnstr_get(x_19, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_19);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8 x_34; 
lean::dec(x_17);
lean::dec(x_15);
x_34 = !lean::is_exclusive(x_8);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_8, 0);
lean::dec(x_35);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_16);
lean::cnstr_set(x_36, 1, x_6);
x_37 = lean::box(0);
lean::cnstr_set(x_8, 0, x_37);
x_38 = lean_nat_add(x_5, x_3);
lean::dec(x_5);
x_5 = x_38;
x_6 = x_36;
goto _start;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_8, 1);
lean::inc(x_40);
lean::dec(x_8);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_16);
lean::cnstr_set(x_41, 1, x_6);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_40);
x_44 = lean_nat_add(x_5, x_3);
lean::dec(x_5);
x_5 = x_44;
x_6 = x_41;
x_8 = x_43;
goto _start;
}
}
}
}
}
obj* l_Lean_Elab_elabOpenHiding(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean::dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = lean::box(0);
lean::cnstr_set(x_9, 0, x_12);
x_13 = l_Lean_Elab_getEnv___rarg(x_9);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = lean::mk_nat_obj(2u);
x_17 = lean_array_get(x_5, x_4, x_16);
lean::cnstr_set(x_13, 0, x_12);
x_18 = lean::box(0);
x_19 = l_Lean_Syntax_getArgs___rarg(x_17);
lean::dec(x_17);
x_20 = lean::mk_nat_obj(1u);
x_21 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_11, x_15, x_20, x_19, x_6, x_18, x_2, x_13);
lean::dec(x_19);
lean::dec(x_15);
if (lean::obj_tag(x_21) == 0)
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_21, 0);
lean::cnstr_set(x_21, 0, x_12);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_11);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_24, x_2, x_21);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_21, 0);
x_27 = lean::cnstr_get(x_21, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_21);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_12);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_11);
lean::cnstr_set(x_29, 1, x_26);
x_30 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_29, x_2, x_28);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_11);
x_31 = !lean::is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_21, 0);
x_33 = lean::cnstr_get(x_21, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_21);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_35 = lean::cnstr_get(x_13, 0);
x_36 = lean::cnstr_get(x_13, 1);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_13);
x_37 = lean::mk_nat_obj(2u);
x_38 = lean_array_get(x_5, x_4, x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_12);
lean::cnstr_set(x_39, 1, x_36);
x_40 = lean::box(0);
x_41 = l_Lean_Syntax_getArgs___rarg(x_38);
lean::dec(x_38);
x_42 = lean::mk_nat_obj(1u);
x_43 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_11, x_35, x_42, x_41, x_6, x_40, x_2, x_39);
lean::dec(x_41);
lean::dec(x_35);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_43, 1);
lean::inc(x_45);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_46 = x_43;
} else {
 lean::dec_ref(x_43);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_12);
lean::cnstr_set(x_47, 1, x_45);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_11);
lean::cnstr_set(x_48, 1, x_44);
x_49 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_48, x_2, x_47);
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_11);
x_50 = lean::cnstr_get(x_43, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_43, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 x_52 = x_43;
} else {
 lean::dec_ref(x_43);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8 x_54; 
lean::dec(x_11);
x_54 = !lean::is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_13, 0);
x_56 = lean::cnstr_get(x_13, 1);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_13);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_58 = lean::cnstr_get(x_9, 0);
x_59 = lean::cnstr_get(x_9, 1);
lean::inc(x_59);
lean::inc(x_58);
lean::dec(x_9);
x_60 = lean::box(0);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_59);
x_62 = l_Lean_Elab_getEnv___rarg(x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_62, 1);
lean::inc(x_64);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_65 = x_62;
} else {
 lean::dec_ref(x_62);
 x_65 = lean::box(0);
}
x_66 = lean::mk_nat_obj(2u);
x_67 = lean_array_get(x_5, x_4, x_66);
if (lean::is_scalar(x_65)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_65;
}
lean::cnstr_set(x_68, 0, x_60);
lean::cnstr_set(x_68, 1, x_64);
x_69 = lean::box(0);
x_70 = l_Lean_Syntax_getArgs___rarg(x_67);
lean::dec(x_67);
x_71 = lean::mk_nat_obj(1u);
x_72 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_58, x_63, x_71, x_70, x_6, x_69, x_2, x_68);
lean::dec(x_70);
lean::dec(x_63);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_72, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_75 = x_72;
} else {
 lean::dec_ref(x_72);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_60);
lean::cnstr_set(x_76, 1, x_74);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_58);
lean::cnstr_set(x_77, 1, x_73);
x_78 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_77, x_2, x_76);
return x_78;
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_58);
x_79 = lean::cnstr_get(x_72, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_72, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_81 = x_72;
} else {
 lean::dec_ref(x_72);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
lean::cnstr_set(x_82, 1, x_80);
return x_82;
}
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_58);
x_83 = lean::cnstr_get(x_62, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_62, 1);
lean::inc(x_84);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_85 = x_62;
} else {
 lean::dec_ref(x_62);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
lean::cnstr_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
uint8 x_87; 
x_87 = !lean::is_exclusive(x_9);
if (x_87 == 0)
{
return x_9;
}
else
{
obj* x_88; obj* x_89; obj* x_90; 
x_88 = lean::cnstr_get(x_9, 0);
x_89 = lean::cnstr_get(x_9, 1);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_9);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_89);
return x_90;
}
}
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenHiding___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Elab_elabOpenHiding___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabOpenHiding(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_4);
x_10 = !lean::is_exclusive(x_7);
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::cnstr_get(x_7, 0);
lean::dec(x_11);
lean::cnstr_set(x_7, 0, x_5);
return x_7;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_5);
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Lean_Syntax_getIdAt___rarg(x_14, x_15);
x_17 = lean::mk_nat_obj(2u);
x_18 = l_Lean_Syntax_getIdAt___rarg(x_14, x_17);
x_19 = l_Lean_Name_append___main(x_1, x_16);
x_20 = l_Lean_Elab_getEnv___rarg(x_7);
if (lean::obj_tag(x_20) == 0)
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; uint8 x_24; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = lean::box(0);
lean::cnstr_set(x_20, 0, x_23);
x_24 = l_Lean_Environment_contains(x_22, x_19);
lean::dec(x_22);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_18);
x_25 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_19, x_6, x_20);
lean::dec(x_14);
if (lean::obj_tag(x_25) == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_25, 0);
lean::cnstr_set(x_25, 0, x_23);
x_28 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_28;
x_5 = x_27;
x_7 = x_25;
goto _start;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = lean::cnstr_get(x_25, 0);
x_31 = lean::cnstr_get(x_25, 1);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_25);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_23);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_33;
x_5 = x_30;
x_7 = x_32;
goto _start;
}
}
else
{
uint8 x_35; 
lean::dec(x_4);
x_35 = !lean::is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_25, 0);
x_37 = lean::cnstr_get(x_25, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_25);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_14);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_18);
lean::cnstr_set(x_39, 1, x_19);
x_40 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_39, x_6, x_20);
if (lean::obj_tag(x_40) == 0)
{
uint8 x_41; 
x_41 = !lean::is_exclusive(x_40);
if (x_41 == 0)
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_40, 0);
lean::cnstr_set(x_40, 0, x_23);
x_43 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_43;
x_5 = x_42;
x_7 = x_40;
goto _start;
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = lean::cnstr_get(x_40, 0);
x_46 = lean::cnstr_get(x_40, 1);
lean::inc(x_46);
lean::inc(x_45);
lean::dec(x_40);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_23);
lean::cnstr_set(x_47, 1, x_46);
x_48 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_48;
x_5 = x_45;
x_7 = x_47;
goto _start;
}
}
else
{
uint8 x_50; 
lean::dec(x_4);
x_50 = !lean::is_exclusive(x_40);
if (x_50 == 0)
{
return x_40;
}
else
{
obj* x_51; obj* x_52; obj* x_53; 
x_51 = lean::cnstr_get(x_40, 0);
x_52 = lean::cnstr_get(x_40, 1);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_40);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; uint8 x_58; 
x_54 = lean::cnstr_get(x_20, 0);
x_55 = lean::cnstr_get(x_20, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_20);
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_55);
x_58 = l_Lean_Environment_contains(x_54, x_19);
lean::dec(x_54);
if (x_58 == 0)
{
obj* x_59; 
lean::dec(x_18);
x_59 = l_Lean_Elab_logUnknownDecl___rarg(x_14, x_19, x_6, x_57);
lean::dec(x_14);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_59, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 x_62 = x_59;
} else {
 lean::dec_ref(x_59);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_56);
lean::cnstr_set(x_63, 1, x_61);
x_64 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_64;
x_5 = x_60;
x_7 = x_63;
goto _start;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_4);
x_66 = lean::cnstr_get(x_59, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_59, 1);
lean::inc(x_67);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 x_68 = x_59;
} else {
 lean::dec_ref(x_59);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_67);
return x_69;
}
}
else
{
obj* x_70; obj* x_71; 
lean::dec(x_14);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_18);
lean::cnstr_set(x_70, 1, x_19);
x_71 = l_Lean_Elab_modifyScope___at_Lean_Elab_addOpenDecl___spec__1(x_70, x_6, x_57);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_71, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_74 = x_71;
} else {
 lean::dec_ref(x_71);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_56);
lean::cnstr_set(x_75, 1, x_73);
x_76 = lean_nat_add(x_4, x_2);
lean::dec(x_4);
x_4 = x_76;
x_5 = x_72;
x_7 = x_75;
goto _start;
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_4);
x_78 = lean::cnstr_get(x_71, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_71, 1);
lean::inc(x_79);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_80 = x_71;
} else {
 lean::dec_ref(x_71);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
lean::cnstr_set(x_81, 1, x_79);
return x_81;
}
}
}
}
else
{
uint8 x_82; 
lean::dec(x_19);
lean::dec(x_18);
lean::dec(x_14);
lean::dec(x_4);
x_82 = !lean::is_exclusive(x_20);
if (x_82 == 0)
{
return x_20;
}
else
{
obj* x_83; obj* x_84; obj* x_85; 
x_83 = lean::cnstr_get(x_20, 0);
x_84 = lean::cnstr_get(x_20, 1);
lean::inc(x_84);
lean::inc(x_83);
lean::dec(x_20);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set(x_85, 1, x_84);
return x_85;
}
}
}
}
}
obj* l_Lean_Elab_elabOpenRenaming(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean::dec(x_7);
x_9 = l_Lean_Elab_resolveNamespace(x_8, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = lean::box(0);
lean::cnstr_set(x_9, 0, x_12);
x_13 = lean::mk_nat_obj(2u);
x_14 = lean_array_get(x_5, x_4, x_13);
x_15 = l_Lean_Syntax_getArgs___rarg(x_14);
lean::dec(x_14);
x_16 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_11, x_13, x_15, x_6, x_12, x_2, x_9);
lean::dec(x_15);
lean::dec(x_11);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_9, 0);
x_18 = lean::cnstr_get(x_9, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_9);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::mk_nat_obj(2u);
x_22 = lean_array_get(x_5, x_4, x_21);
x_23 = l_Lean_Syntax_getArgs___rarg(x_22);
lean::dec(x_22);
x_24 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_17, x_21, x_23, x_6, x_19, x_2, x_20);
lean::dec(x_23);
lean::dec(x_17);
return x_24;
}
}
else
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_9, 0);
x_27 = lean::cnstr_get(x_9, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_9);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabOpenRenaming___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_Elab_elabOpenRenaming___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabOpenRenaming(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elab_elabOpen(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_asNode___rarg(x_7);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
x_11 = lean_name_dec_eq(x_9, x_10);
if (x_11 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
x_13 = lean_name_dec_eq(x_9, x_12);
if (x_13 == 0)
{
obj* x_14; uint8 x_15; 
x_14 = l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
x_15 = lean_name_dec_eq(x_9, x_14);
lean::dec(x_9);
if (x_15 == 0)
{
obj* x_16; 
x_16 = l_Lean_Elab_elabOpenRenaming(x_8, x_2, x_3);
lean::dec(x_8);
return x_16;
}
else
{
obj* x_17; 
x_17 = l_Lean_Elab_elabOpenHiding(x_8, x_2, x_3);
lean::dec(x_8);
return x_17;
}
}
else
{
obj* x_18; 
lean::dec(x_9);
x_18 = l_Lean_Elab_elabOpenOnly(x_8, x_2, x_3);
lean::dec(x_8);
return x_18;
}
}
else
{
obj* x_19; 
lean::dec(x_9);
x_19 = l_Lean_Elab_elabOpenSimple(x_8, x_2, x_3);
lean::dec(x_8);
return x_19;
}
}
}
obj* l_Lean_Elab_elabOpen___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabOpen(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabOpen");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabOpen___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabOpen(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_open___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
x_7 = lean::cnstr_get(x_5, 5);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::dec(x_1);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_5, 5);
lean::dec(x_9);
x_10 = lean::box(0);
lean::cnstr_set(x_3, 0, x_10);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
x_13 = lean::cnstr_get(x_5, 2);
x_14 = lean::cnstr_get(x_5, 3);
x_15 = lean::cnstr_get(x_5, 4);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_12);
lean::cnstr_set(x_16, 2, x_13);
lean::cnstr_set(x_16, 3, x_14);
lean::cnstr_set(x_16, 4, x_15);
lean::cnstr_set(x_16, 5, x_7);
x_17 = lean::box(0);
lean::cnstr_set(x_3, 1, x_16);
lean::cnstr_set(x_3, 0, x_17);
return x_3;
}
}
else
{
obj* x_18; uint8 x_19; 
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
x_19 = !lean::is_exclusive(x_5);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = lean::cnstr_get(x_5, 5);
lean::dec(x_20);
x_21 = !lean::is_exclusive(x_7);
if (x_21 == 0)
{
obj* x_22; obj* x_23; uint8 x_24; 
x_22 = lean::cnstr_get(x_7, 1);
x_23 = lean::cnstr_get(x_7, 0);
lean::dec(x_23);
x_24 = !lean::is_exclusive(x_18);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = lean::cnstr_get(x_18, 5);
lean::cnstr_set(x_7, 1, x_25);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_18, 5, x_7);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_18);
lean::cnstr_set(x_26, 1, x_22);
lean::cnstr_set(x_5, 5, x_26);
x_27 = lean::box(0);
lean::cnstr_set(x_3, 0, x_27);
return x_3;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_28 = lean::cnstr_get(x_18, 0);
x_29 = lean::cnstr_get(x_18, 1);
x_30 = lean::cnstr_get(x_18, 2);
x_31 = lean::cnstr_get(x_18, 3);
x_32 = lean::cnstr_get(x_18, 4);
x_33 = lean::cnstr_get(x_18, 5);
x_34 = lean::cnstr_get(x_18, 6);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_18);
lean::cnstr_set(x_7, 1, x_33);
lean::cnstr_set(x_7, 0, x_1);
x_35 = lean::alloc_cnstr(0, 7, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_29);
lean::cnstr_set(x_35, 2, x_30);
lean::cnstr_set(x_35, 3, x_31);
lean::cnstr_set(x_35, 4, x_32);
lean::cnstr_set(x_35, 5, x_7);
lean::cnstr_set(x_35, 6, x_34);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_22);
lean::cnstr_set(x_5, 5, x_36);
x_37 = lean::box(0);
lean::cnstr_set(x_3, 0, x_37);
return x_3;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_38 = lean::cnstr_get(x_7, 1);
lean::inc(x_38);
lean::dec(x_7);
x_39 = lean::cnstr_get(x_18, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_18, 1);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_18, 2);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_18, 3);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_18, 4);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_18, 5);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_18, 6);
lean::inc(x_45);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 lean::cnstr_release(x_18, 2);
 lean::cnstr_release(x_18, 3);
 lean::cnstr_release(x_18, 4);
 lean::cnstr_release(x_18, 5);
 lean::cnstr_release(x_18, 6);
 x_46 = x_18;
} else {
 lean::dec_ref(x_18);
 x_46 = lean::box(0);
}
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_1);
lean::cnstr_set(x_47, 1, x_44);
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_39);
lean::cnstr_set(x_48, 1, x_40);
lean::cnstr_set(x_48, 2, x_41);
lean::cnstr_set(x_48, 3, x_42);
lean::cnstr_set(x_48, 4, x_43);
lean::cnstr_set(x_48, 5, x_47);
lean::cnstr_set(x_48, 6, x_45);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_38);
lean::cnstr_set(x_5, 5, x_49);
x_50 = lean::box(0);
lean::cnstr_set(x_3, 0, x_50);
return x_3;
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_51 = lean::cnstr_get(x_5, 0);
x_52 = lean::cnstr_get(x_5, 1);
x_53 = lean::cnstr_get(x_5, 2);
x_54 = lean::cnstr_get(x_5, 3);
x_55 = lean::cnstr_get(x_5, 4);
lean::inc(x_55);
lean::inc(x_54);
lean::inc(x_53);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_5);
x_56 = lean::cnstr_get(x_7, 1);
lean::inc(x_56);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_57 = x_7;
} else {
 lean::dec_ref(x_7);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_18, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_18, 1);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_18, 2);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_18, 3);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_18, 4);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_18, 5);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_18, 6);
lean::inc(x_64);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 lean::cnstr_release(x_18, 2);
 lean::cnstr_release(x_18, 3);
 lean::cnstr_release(x_18, 4);
 lean::cnstr_release(x_18, 5);
 lean::cnstr_release(x_18, 6);
 x_65 = x_18;
} else {
 lean::dec_ref(x_18);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_57;
}
lean::cnstr_set(x_66, 0, x_1);
lean::cnstr_set(x_66, 1, x_63);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_58);
lean::cnstr_set(x_67, 1, x_59);
lean::cnstr_set(x_67, 2, x_60);
lean::cnstr_set(x_67, 3, x_61);
lean::cnstr_set(x_67, 4, x_62);
lean::cnstr_set(x_67, 5, x_66);
lean::cnstr_set(x_67, 6, x_64);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_56);
x_69 = lean::alloc_cnstr(0, 6, 0);
lean::cnstr_set(x_69, 0, x_51);
lean::cnstr_set(x_69, 1, x_52);
lean::cnstr_set(x_69, 2, x_53);
lean::cnstr_set(x_69, 3, x_54);
lean::cnstr_set(x_69, 4, x_55);
lean::cnstr_set(x_69, 5, x_68);
x_70 = lean::box(0);
lean::cnstr_set(x_3, 1, x_69);
lean::cnstr_set(x_3, 0, x_70);
return x_3;
}
}
}
else
{
obj* x_71; obj* x_72; 
x_71 = lean::cnstr_get(x_3, 1);
lean::inc(x_71);
lean::dec(x_3);
x_72 = lean::cnstr_get(x_71, 5);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_1);
x_73 = lean::cnstr_get(x_71, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_71, 2);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_71, 3);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_71, 4);
lean::inc(x_77);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 lean::cnstr_release(x_71, 2);
 lean::cnstr_release(x_71, 3);
 lean::cnstr_release(x_71, 4);
 lean::cnstr_release(x_71, 5);
 x_78 = x_71;
} else {
 lean::dec_ref(x_71);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_73);
lean::cnstr_set(x_79, 1, x_74);
lean::cnstr_set(x_79, 2, x_75);
lean::cnstr_set(x_79, 3, x_76);
lean::cnstr_set(x_79, 4, x_77);
lean::cnstr_set(x_79, 5, x_72);
x_80 = lean::box(0);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_79);
return x_81;
}
else
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_82 = lean::cnstr_get(x_72, 0);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_71, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_71, 1);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_71, 2);
lean::inc(x_85);
x_86 = lean::cnstr_get(x_71, 3);
lean::inc(x_86);
x_87 = lean::cnstr_get(x_71, 4);
lean::inc(x_87);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 lean::cnstr_release(x_71, 2);
 lean::cnstr_release(x_71, 3);
 lean::cnstr_release(x_71, 4);
 lean::cnstr_release(x_71, 5);
 x_88 = x_71;
} else {
 lean::dec_ref(x_71);
 x_88 = lean::box(0);
}
x_89 = lean::cnstr_get(x_72, 1);
lean::inc(x_89);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_90 = x_72;
} else {
 lean::dec_ref(x_72);
 x_90 = lean::box(0);
}
x_91 = lean::cnstr_get(x_82, 0);
lean::inc(x_91);
x_92 = lean::cnstr_get(x_82, 1);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_82, 2);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_82, 3);
lean::inc(x_94);
x_95 = lean::cnstr_get(x_82, 4);
lean::inc(x_95);
x_96 = lean::cnstr_get(x_82, 5);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_82, 6);
lean::inc(x_97);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 lean::cnstr_release(x_82, 2);
 lean::cnstr_release(x_82, 3);
 lean::cnstr_release(x_82, 4);
 lean::cnstr_release(x_82, 5);
 lean::cnstr_release(x_82, 6);
 x_98 = x_82;
} else {
 lean::dec_ref(x_82);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_90;
}
lean::cnstr_set(x_99, 0, x_1);
lean::cnstr_set(x_99, 1, x_96);
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 7, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_91);
lean::cnstr_set(x_100, 1, x_92);
lean::cnstr_set(x_100, 2, x_93);
lean::cnstr_set(x_100, 3, x_94);
lean::cnstr_set(x_100, 4, x_95);
lean::cnstr_set(x_100, 5, x_99);
lean::cnstr_set(x_100, 6, x_97);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_89);
if (lean::is_scalar(x_88)) {
 x_102 = lean::alloc_cnstr(0, 6, 0);
} else {
 x_102 = x_88;
}
lean::cnstr_set(x_102, 0, x_83);
lean::cnstr_set(x_102, 1, x_84);
lean::cnstr_set(x_102, 2, x_85);
lean::cnstr_set(x_102, 3, x_86);
lean::cnstr_set(x_102, 4, x_87);
lean::cnstr_set(x_102, 5, x_101);
x_103 = lean::box(0);
x_104 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_102);
return x_104;
}
}
}
}
obj* _init_l_Lean_Elab_addUniverse___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("a universe named '");
return x_1;
}
}
obj* _init_l_Lean_Elab_addUniverse___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' has already been declared in this Scope");
return x_1;
}
}
obj* l_Lean_Elab_addUniverse(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Syntax_getId___rarg(x_1);
x_5 = l_Lean_Elab_getUniverses___rarg(x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
x_9 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_4, x_7);
lean::dec(x_7);
if (x_9 == 0)
{
obj* x_10; 
x_10 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_4, x_2, x_5);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_4);
x_13 = l_Lean_Elab_addUniverse___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean::dec(x_12);
x_15 = l_Lean_Elab_addUniverse___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_Elab_logError___rarg(x_1, x_16, x_2, x_5);
return x_17;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_18 = lean::cnstr_get(x_5, 0);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_5);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
x_22 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_4, x_18);
lean::dec(x_18);
if (x_22 == 0)
{
obj* x_23; 
x_23 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_4, x_2, x_21);
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_4);
x_26 = l_Lean_Elab_addUniverse___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean::dec(x_25);
x_28 = l_Lean_Elab_addUniverse___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_Elab_logError___rarg(x_1, x_29, x_2, x_21);
return x_30;
}
}
}
else
{
uint8 x_31; 
lean::dec(x_4);
x_31 = !lean::is_exclusive(x_5);
if (x_31 == 0)
{
return x_5;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_5, 0);
x_33 = lean::cnstr_get(x_5, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_5);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
}
obj* l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_modifyScope___at_Lean_Elab_addUniverse___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Elab_addUniverse___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_addUniverse(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Elab_elabUniverse(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Elab_addUniverse(x_7, x_2, x_3);
lean::dec(x_7);
return x_8;
}
}
obj* l_Lean_Elab_elabUniverse___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabUniverse(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabUniverse");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabUniverse___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverse(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_universe___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_3);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
lean::cnstr_set(x_6, 0, x_4);
return x_6;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_4);
x_13 = lean_array_fget(x_2, x_3);
x_14 = l_Lean_Elab_addUniverse(x_13, x_5, x_6);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_14, 0);
x_17 = lean::box(0);
lean::cnstr_set(x_14, 0, x_17);
x_18 = lean_nat_add(x_3, x_1);
lean::dec(x_3);
x_3 = x_18;
x_4 = x_16;
x_6 = x_14;
goto _start;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_14, 0);
x_21 = lean::cnstr_get(x_14, 1);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_14);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
x_24 = lean_nat_add(x_3, x_1);
lean::dec(x_3);
x_3 = x_24;
x_4 = x_20;
x_6 = x_23;
goto _start;
}
}
else
{
uint8 x_26; 
lean::dec(x_3);
x_26 = !lean::is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_14, 0);
x_28 = lean::cnstr_get(x_14, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_14);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
obj* l_Lean_Elab_elabUniverses(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getArgs___rarg(x_7);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::box(0);
x_11 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(x_6, x_8, x_9, x_10, x_2, x_3);
lean::dec(x_8);
return x_11;
}
}
obj* l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Syntax_mfoldArgsAux___main___at_Lean_Elab_elabUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Elab_elabUniverses___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabUniverses(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabUniverses");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabUniverses___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabUniverses(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_universes___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_elabInitQuot___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_getEnv___rarg(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = lean::box(4);
x_8 = lean_add_decl(x_5, x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = l_Lean_Elab_logElabException(x_10, x_1, x_3);
return x_11;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_13 = l_Lean_Elab_setEnv(x_12, x_1, x_3);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_3, 0);
x_15 = lean::cnstr_get(x_3, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_3);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::box(4);
x_19 = lean_add_decl(x_14, x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
lean::dec(x_19);
x_21 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = l_Lean_Elab_logElabException(x_21, x_1, x_17);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_19, 0);
lean::inc(x_23);
lean::dec(x_19);
x_24 = l_Lean_Elab_setEnv(x_23, x_1, x_17);
return x_24;
}
}
}
else
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_3);
if (x_25 == 0)
{
return x_3;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_3, 0);
x_27 = lean::cnstr_get(x_3, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_3);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
}
}
obj* l_Lean_Elab_elabInitQuot(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabInitQuot___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Elab_elabInitQuot___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_elabInitQuot___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Elab_elabInitQuot___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Elab_elabInitQuot(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabInitQuot");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabInitQuot___boxed), 1, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabInitQuot(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_init__quot___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_elabVariable(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at___private_init_lean_parser_module_4__testModuleParserAux___main___spec__1), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_runIOUnsafe___rarg(x_4, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::dec(x_7);
x_8 = lean::box(0);
lean::cnstr_set(x_5, 0, x_8);
return x_5;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_5, 0);
x_14 = lean::cnstr_get(x_5, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_5);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
}
obj* l_Lean_Elab_elabVariable___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabVariable(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabVariable");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabVariable___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabVariable(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_variable___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(uint8 x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_1, x_5);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
x_9 = l_Nat_repr(x_7);
x_10 = l_Prod_HasRepr___rarg___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean::dec(x_9);
x_12 = l_List_reprAux___main___rarg___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_8);
x_16 = lean_string_append(x_13, x_15);
lean::dec(x_15);
x_17 = l_Option_HasRepr___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_12, x_18);
lean::dec(x_18);
x_20 = lean_string_append(x_19, x_6);
lean::dec(x_6);
return x_20;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_21; 
x_21 = l_String_splitAux___main___closed__1;
return x_21;
}
else
{
obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_2, 1);
lean::inc(x_23);
lean::dec(x_2);
x_24 = 0;
x_25 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_24, x_23);
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_28 = l_Nat_repr(x_26);
x_29 = l_Prod_HasRepr___rarg___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean::dec(x_28);
x_31 = l_List_reprAux___main___rarg___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_27);
x_35 = lean_string_append(x_32, x_34);
lean::dec(x_34);
x_36 = l_Option_HasRepr___rarg___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_25);
lean::dec(x_25);
return x_38;
}
}
}
}
obj* l_List_toString___at_Lean_Elab_elabResolveName___spec__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean::dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
obj* l_Lean_Elab_elabResolveName(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_Syntax_getId___rarg(x_7);
lean::dec(x_7);
x_9 = l_Lean_Elab_resolveName(x_8, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = lean::box(0);
lean::cnstr_set(x_9, 0, x_12);
x_13 = lean::box(0);
x_14 = l_Lean_Elab_getPosition(x_13, x_2, x_9);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_16 = lean::cnstr_get(x_14, 0);
lean::cnstr_set(x_14, 0, x_12);
x_17 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_11);
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_20 = l_Nat_repr(x_18);
x_21 = l_Sigma_HasRepr___rarg___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean::dec(x_20);
x_23 = l_List_reprAux___main___rarg___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Nat_repr(x_19);
x_26 = lean_string_append(x_24, x_25);
lean::dec(x_25);
x_27 = l_Sigma_HasRepr___rarg___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_Format_flatten___main___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_17);
lean::dec(x_17);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean::closure_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_runIOUnsafe___rarg(x_32, x_2, x_14);
if (lean::obj_tag(x_33) == 0)
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_33);
if (x_34 == 0)
{
obj* x_35; 
x_35 = lean::cnstr_get(x_33, 0);
lean::dec(x_35);
lean::cnstr_set(x_33, 0, x_12);
return x_33;
}
else
{
obj* x_36; obj* x_37; 
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_12);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8 x_38; 
x_38 = !lean::is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_33, 0);
x_40 = lean::cnstr_get(x_33, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_33);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_42 = lean::cnstr_get(x_14, 0);
x_43 = lean::cnstr_get(x_14, 1);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_14);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_12);
lean::cnstr_set(x_44, 1, x_43);
x_45 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_11);
x_46 = lean::cnstr_get(x_42, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
lean::dec(x_42);
x_48 = l_Nat_repr(x_46);
x_49 = l_Sigma_HasRepr___rarg___closed__1;
x_50 = lean_string_append(x_49, x_48);
lean::dec(x_48);
x_51 = l_List_reprAux___main___rarg___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = l_Nat_repr(x_47);
x_54 = lean_string_append(x_52, x_53);
lean::dec(x_53);
x_55 = l_Sigma_HasRepr___rarg___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_Lean_Format_flatten___main___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_45);
lean::dec(x_45);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean::closure_set(x_60, 0, x_59);
x_61 = l_Lean_Elab_runIOUnsafe___rarg(x_60, x_2, x_44);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_63 = x_61;
} else {
 lean::dec_ref(x_61);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_12);
lean::cnstr_set(x_64, 1, x_62);
return x_64;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_65 = lean::cnstr_get(x_61, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_67 = x_61;
} else {
 lean::dec_ref(x_61);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
uint8 x_69; 
lean::dec(x_11);
x_69 = !lean::is_exclusive(x_14);
if (x_69 == 0)
{
return x_14;
}
else
{
obj* x_70; obj* x_71; obj* x_72; 
x_70 = lean::cnstr_get(x_14, 0);
x_71 = lean::cnstr_get(x_14, 1);
lean::inc(x_71);
lean::inc(x_70);
lean::dec(x_14);
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_73 = lean::cnstr_get(x_9, 0);
x_74 = lean::cnstr_get(x_9, 1);
lean::inc(x_74);
lean::inc(x_73);
lean::dec(x_9);
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_74);
x_77 = lean::box(0);
x_78 = l_Lean_Elab_getPosition(x_77, x_2, x_76);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_78, 1);
lean::inc(x_80);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_release(x_78, 1);
 x_81 = x_78;
} else {
 lean::dec_ref(x_78);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_75);
lean::cnstr_set(x_82, 1, x_80);
x_83 = l_List_toString___at_Lean_Elab_elabResolveName___spec__1(x_73);
x_84 = lean::cnstr_get(x_79, 0);
lean::inc(x_84);
x_85 = lean::cnstr_get(x_79, 1);
lean::inc(x_85);
lean::dec(x_79);
x_86 = l_Nat_repr(x_84);
x_87 = l_Sigma_HasRepr___rarg___closed__1;
x_88 = lean_string_append(x_87, x_86);
lean::dec(x_86);
x_89 = l_List_reprAux___main___rarg___closed__1;
x_90 = lean_string_append(x_88, x_89);
x_91 = l_Nat_repr(x_85);
x_92 = lean_string_append(x_90, x_91);
lean::dec(x_91);
x_93 = l_Sigma_HasRepr___rarg___closed__2;
x_94 = lean_string_append(x_92, x_93);
x_95 = l_Lean_Format_flatten___main___closed__1;
x_96 = lean_string_append(x_94, x_95);
x_97 = lean_string_append(x_96, x_83);
lean::dec(x_83);
x_98 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean::closure_set(x_98, 0, x_97);
x_99 = l_Lean_Elab_runIOUnsafe___rarg(x_98, x_2, x_82);
if (lean::obj_tag(x_99) == 0)
{
obj* x_100; obj* x_101; obj* x_102; 
x_100 = lean::cnstr_get(x_99, 1);
lean::inc(x_100);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_101 = x_99;
} else {
 lean::dec_ref(x_99);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_75);
lean::cnstr_set(x_102, 1, x_100);
return x_102;
}
else
{
obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_103 = lean::cnstr_get(x_99, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_99, 1);
lean::inc(x_104);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_105 = x_99;
} else {
 lean::dec_ref(x_99);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_104);
return x_106;
}
}
else
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_73);
x_107 = lean::cnstr_get(x_78, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get(x_78, 1);
lean::inc(x_108);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_release(x_78, 1);
 x_109 = x_78;
} else {
 lean::dec_ref(x_78);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
uint8 x_111; 
x_111 = !lean::is_exclusive(x_9);
if (x_111 == 0)
{
return x_9;
}
else
{
obj* x_112; obj* x_113; obj* x_114; 
x_112 = lean::cnstr_get(x_9, 0);
x_113 = lean::cnstr_get(x_9, 1);
lean::inc(x_113);
lean::inc(x_112);
lean::dec(x_9);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_112);
lean::cnstr_set(x_114, 1, x_113);
return x_114;
}
}
}
}
obj* l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Elab_elabResolveName___spec__2(x_3, x_2);
return x_4;
}
}
obj* l_Lean_Elab_elabResolveName___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabResolveName(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabResolveName");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabResolveName___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabResolveName(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_resolve__name___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_elabPreTerm(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = x_7;
lean::inc(x_2);
x_9 = l_Lean_Elab_toPreTerm(x_8, x_2, x_3);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = lean::box(0);
lean::cnstr_set(x_9, 0, x_12);
x_13 = lean_expr_dbg_to_string(x_11);
lean::dec(x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = l_Lean_Elab_runIOUnsafe___rarg(x_14, x_2, x_9);
lean::dec(x_2);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; 
x_17 = lean::cnstr_get(x_15, 0);
lean::dec(x_17);
lean::cnstr_set(x_15, 0, x_12);
return x_15;
}
else
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_15, 0);
x_22 = lean::cnstr_get(x_15, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_15);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_9, 0);
x_25 = lean::cnstr_get(x_9, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_9);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = lean_expr_dbg_to_string(x_24);
lean::dec(x_24);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean::closure_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_runIOUnsafe___rarg(x_29, x_2, x_27);
lean::dec(x_2);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_32 = x_30;
} else {
 lean::dec_ref(x_30);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_26);
lean::cnstr_set(x_33, 1, x_31);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = lean::cnstr_get(x_30, 0);
lean::inc(x_34);
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_36 = x_30;
} else {
 lean::dec_ref(x_30);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8 x_38; 
lean::dec(x_2);
x_38 = !lean::is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_9, 0);
x_40 = lean::cnstr_get(x_9, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_9);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
return x_41;
}
}
}
}
obj* l_Lean_Elab_elabPreTerm___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabPreTerm(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabPreTerm");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabPreTerm___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabPreTerm(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_preterm___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* _init_l_Lean_Elab_elabElab___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed to elaborate syntax");
return x_1;
}
}
obj* _init_l_Lean_Elab_elabElab___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Elab_elabElab___closed__1;
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Elab_elabElab(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::box(0);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean_array_get(x_6, x_4, x_7);
x_9 = x_8;
x_10 = 0;
lean::inc(x_2);
x_11 = l_Lean_Elab_elabTermAux___main(x_9, x_5, x_10, x_2, x_3);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 4)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_11);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_11, 0);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_16 = lean::box(0);
lean::cnstr_set(x_11, 0, x_16);
x_17 = lean_expr_dbg_to_string(x_15);
lean::dec(x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_runIOUnsafe___rarg(x_18, x_2, x_11);
lean::dec(x_2);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_20 = lean::cnstr_get(x_11, 1);
lean::inc(x_20);
lean::dec(x_11);
x_21 = lean::cnstr_get(x_12, 0);
lean::inc(x_21);
lean::dec(x_12);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
x_24 = lean_expr_dbg_to_string(x_21);
lean::dec(x_21);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_IO_println___at_HasRepr_HasEval___spec__1___boxed), 2, 1);
lean::closure_set(x_25, 0, x_24);
x_26 = l_Lean_Elab_runIOUnsafe___rarg(x_25, x_2, x_23);
lean::dec(x_2);
return x_26;
}
}
else
{
uint8 x_27; 
lean::dec(x_12);
lean::dec(x_2);
x_27 = !lean::is_exclusive(x_11);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_11, 0);
lean::dec(x_28);
x_29 = l_Lean_Elab_elabElab___closed__2;
lean::cnstr_set_tag(x_11, 1);
lean::cnstr_set(x_11, 0, x_29);
return x_11;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_11, 1);
lean::inc(x_30);
lean::dec(x_11);
x_31 = l_Lean_Elab_elabElab___closed__2;
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8 x_33; 
lean::dec(x_2);
x_33 = !lean::is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_11, 0);
x_35 = lean::cnstr_get(x_11, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_11);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
}
obj* l_Lean_Elab_elabElab___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Elab_elabElab(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabElab");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabElab___boxed), 3, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabElab(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_elab___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_elabMixfix___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = lean::box(0);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_elabMixfix(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabMixfix___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_elabMixfix___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_elabMixfix(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabMixfix");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabMixfix___boxed), 2, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabMixfix(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_mixfix___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_elabReserve___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = lean::box(0);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_elabReserve(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabReserve___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_elabReserve___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_elabReserve(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabReserve");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabReserve___boxed), 2, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabReserve(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_reserve___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* l_Lean_Elab_elabNotation___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = lean::box(0);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_elabNotation(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabNotation___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_elabNotation___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_elabNotation(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elabNotation");
return x_1;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l___regBuiltinTermElab_Lean_Elab_convertType___closed__2;
x_2 = l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_elabNotation___boxed), 2, 0);
return x_1;
}
}
obj* l___regBuiltinTermElab_Lean_Elab_elabNotation(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Command_notation___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3;
x_5 = l_Lean_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
obj* initialize_init_lean_elaborator_alias(obj*);
obj* initialize_init_lean_elaborator_basic(obj*);
obj* initialize_init_lean_elaborator_resolvename(obj*);
obj* initialize_init_lean_elaborator_term(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_elaborator_command(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_alias(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_basic(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_resolvename(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_term(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNamespace___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabNamespace(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabSection___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabSection(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Elab_elabEnd___closed__1 = _init_l_Lean_Elab_elabEnd___closed__1();
lean::mark_persistent(l_Lean_Elab_elabEnd___closed__1);
l_Lean_Elab_elabEnd___closed__2 = _init_l_Lean_Elab_elabEnd___closed__2();
lean::mark_persistent(l_Lean_Elab_elabEnd___closed__2);
l_Lean_Elab_elabEnd___closed__3 = _init_l_Lean_Elab_elabEnd___closed__3();
lean::mark_persistent(l_Lean_Elab_elabEnd___closed__3);
l_Lean_Elab_elabEnd___closed__4 = _init_l_Lean_Elab_elabEnd___closed__4();
lean::mark_persistent(l_Lean_Elab_elabEnd___closed__4);
l_Lean_Elab_elabEnd___closed__5 = _init_l_Lean_Elab_elabEnd___closed__5();
lean::mark_persistent(l_Lean_Elab_elabEnd___closed__5);
l_Lean_Elab_elabEnd___closed__6 = _init_l_Lean_Elab_elabEnd___closed__6();
lean::mark_persistent(l_Lean_Elab_elabEnd___closed__6);
l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabEnd___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabEnd(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Elab_elabExport___closed__1 = _init_l_Lean_Elab_elabExport___closed__1();
lean::mark_persistent(l_Lean_Elab_elabExport___closed__1);
l_Lean_Elab_elabExport___closed__2 = _init_l_Lean_Elab_elabExport___closed__2();
lean::mark_persistent(l_Lean_Elab_elabExport___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabExport___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabExport___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabExport___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabExport(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabOpen___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabOpen(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Elab_addUniverse___closed__1 = _init_l_Lean_Elab_addUniverse___closed__1();
lean::mark_persistent(l_Lean_Elab_addUniverse___closed__1);
l_Lean_Elab_addUniverse___closed__2 = _init_l_Lean_Elab_addUniverse___closed__2();
lean::mark_persistent(l_Lean_Elab_addUniverse___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverse___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabUniverse(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabUniverses___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabUniverses(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabInitQuot___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabInitQuot(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabVariable___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabVariable(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabResolveName___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabResolveName(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabPreTerm___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabPreTerm(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Elab_elabElab___closed__1 = _init_l_Lean_Elab_elabElab___closed__1();
lean::mark_persistent(l_Lean_Elab_elabElab___closed__1);
l_Lean_Elab_elabElab___closed__2 = _init_l_Lean_Elab_elabElab___closed__2();
lean::mark_persistent(l_Lean_Elab_elabElab___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabElab___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabElab___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabElab___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabElab(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabMixfix___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabMixfix(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabReserve___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabReserve(w);
if (lean::io_result_is_error(w)) return w;
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__1);
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__2);
l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3();
lean::mark_persistent(l___regBuiltinTermElab_Lean_Elab_elabNotation___closed__3);
w = l___regBuiltinTermElab_Lean_Elab_elabNotation(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
}
