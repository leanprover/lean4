// Lean compiler output
// Module: Lean.Elab.MacroRules
// Imports: Init Lean.Elab.Syntax Lean.Elab.AuxDef
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
uint8_t l_Lean_Syntax_isQuot(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__34;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__1(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__48;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__7;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__15;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__50;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__22;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__18;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__15;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5;
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__14;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__14;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__28;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMacroRulesAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__30;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__5;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__33;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__13;
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__23;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__8;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__41;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__52;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__54;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMacroRulesAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__1;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__45;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__27;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__40;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__25;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__36;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__29;
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__37;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__53;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__42;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__55;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__8;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__3;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__56;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__43;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__12;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__32;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__10;
static lean_object* l_Lean_Elab_Command_elabMacroRules___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__46;
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__16;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__4;
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__11;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMacroRulesAux___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMacroRulesAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___rarg(lean_object*);
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__4;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__16;
lean_object* l_Array_mkArray5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__6;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__49;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__2;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__31;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__7;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__7;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg(lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__1;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__58;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__26;
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
lean_object* l_Array_mkArray6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__35;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__6;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__38;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMacroRulesAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__4;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__10;
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__9;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__19;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__51;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__44;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__1;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__47;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__7;
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__3;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__3;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__12;
static lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__5;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__17;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__4;
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__57;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabMacroRulesAux___closed__8;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMacroRulesAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMacroRulesAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabMacroRulesAux___spec__3(x_2, x_3, x_4, x_8);
lean_dec(x_4);
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
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabMacroRulesAux___spec__3(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMacroRulesAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
lean_inc(x_8);
x_9 = l_Lean_Syntax_getKind(x_8);
x_10 = l_Lean_Elab_Command_checkRuleKind(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
{
size_t _tmp_4 = x_12;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("|", 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=>", 2);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("choice", 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid macro_rules alternative, unexpected syntax node kind '", 62);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__12() {
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__13;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid macro_rules alternative, expected syntax node kind '", 60);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_1);
x_53 = l_Lean_Syntax_getQuotContent(x_1);
lean_inc(x_53);
x_54 = l_Lean_Syntax_getKind(x_53);
x_55 = l_Lean_Elab_Command_checkRuleKind(x_54, x_5);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__7;
x_57 = lean_name_eq(x_54, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_58, 0, x_54);
x_59 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__9;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__11;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMacroRulesAux___spec__2(x_6, x_62, x_8, x_9, x_10);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
x_64 = l_Lean_Syntax_getArgs(x_53);
lean_dec(x_53);
x_65 = lean_array_get_size(x_64);
x_66 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_67 = 0;
x_68 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__12;
x_69 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMacroRulesAux___spec__4(x_5, x_68, x_64, x_66, x_67, x_68);
lean_dec(x_64);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__14;
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_72, 0, x_5);
x_73 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__16;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__11;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMacroRulesAux___spec__2(x_6, x_76, x_8, x_9, x_10);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec(x_6);
lean_dec(x_5);
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
x_11 = x_78;
goto block_52;
}
}
else
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
lean_dec(x_70);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_80, 0, x_5);
x_81 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__16;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__11;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMacroRulesAux___spec__2(x_6, x_84, x_8, x_9, x_10);
return x_85;
}
else
{
lean_object* x_86; 
lean_dec(x_6);
lean_dec(x_5);
x_86 = lean_ctor_get(x_79, 0);
lean_inc(x_86);
lean_dec(x_79);
x_11 = x_86;
goto block_52;
}
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_6);
lean_ctor_set(x_87, 1, x_10);
return x_87;
}
block_52:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_setArg(x_1, x_12, x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_set(x_2, x_14, x_13);
x_16 = l_Lean_Elab_Command_getRef(x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_17, x_19);
x_21 = l_Lean_Elab_Command_getCurrMacroScope(x_8, x_9, x_18);
lean_dec(x_8);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Command_getMainModule___rarg(x_9, x_22);
lean_dec(x_9);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_20);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
x_29 = l_Array_append___rarg(x_28, x_15);
x_30 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_20);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_29);
x_32 = l_Array_mkArray1___rarg(x_31);
lean_inc(x_20);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_32);
x_34 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5;
lean_inc(x_20);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Array_mkArray4___rarg(x_27, x_33, x_35, x_3);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_23, 0, x_37);
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_dec(x_23);
x_39 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_20);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
x_42 = l_Array_append___rarg(x_41, x_15);
x_43 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_20);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_20);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
x_45 = l_Array_mkArray1___rarg(x_44);
lean_inc(x_20);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_20);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_45);
x_47 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5;
lean_inc(x_20);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_20);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Array_mkArray4___rarg(x_40, x_46, x_48, x_3);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_20);
lean_ctor_set(x_50, 1, x_4);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
return x_51;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlt", 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_uget(x_4, x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_4, x_3, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__5;
lean_inc(x_10);
x_14 = l_Lean_Syntax_isOfKind(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg(x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_10, x_20);
lean_inc(x_21);
x_22 = l_Lean_Syntax_matchesNull(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg(x_7);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_52; uint8_t x_53; 
x_28 = l_Lean_Syntax_getArg(x_21, x_11);
lean_dec(x_21);
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Syntax_getArg(x_10, x_29);
x_31 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_52 = lean_array_get_size(x_31);
x_53 = lean_nat_dec_lt(x_11, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_instInhabitedSyntax;
x_55 = l___private_Init_Util_0__outOfBounds___rarg(x_54);
x_32 = x_55;
goto block_51;
}
else
{
lean_object* x_56; 
x_56 = lean_array_fget(x_31, x_11);
x_32 = x_56;
goto block_51;
}
block_51:
{
uint8_t x_33; 
x_33 = l_Lean_Syntax_isQuot(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_34 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg(x_7);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_40 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2(x_32, x_31, x_30, x_13, x_1, x_10, x_39, x_5, x_6, x_7);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = 1;
x_44 = lean_usize_add(x_3, x_43);
x_45 = lean_array_uset(x_12, x_3, x_41);
x_3 = x_44;
x_4 = x_45;
x_7 = x_42;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
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
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attrInstance", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Attr", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("macro", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Lean_Elab_Command_elabMacroRulesAux___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("aux_def", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__6;
x_3 = l_Lean_Elab_Command_elabMacroRulesAux___closed__7;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attributes", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@[", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("macroRules", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMacroRulesAux___closed__14;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Macro", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMacroRulesAux___closed__18;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__18;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMacroRulesAux___closed__21;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabMacroRulesAux___closed__22;
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fun", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__27;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlts", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__29;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__31;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("noErrorIfUnused", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__34;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("no_error_if_unused%", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__37;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("throw", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("MonadExcept", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabMacroRulesAux___closed__42;
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__43;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__44;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Macro.Exception.unsupportedSyntax", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMacroRulesAux___closed__46;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Exception", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unsupportedSyntax", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__18;
x_3 = l_Lean_Elab_Command_elabMacroRulesAux___closed__48;
x_4 = l_Lean_Elab_Command_elabMacroRulesAux___closed__49;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__50;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMacroRulesAux___closed__50;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__52;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabMacroRulesAux___closed__51;
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__53;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__57() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__57;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5(x_5, x_11, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_getRef(x_7, x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_17, x_19);
x_21 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Command_elabMacroRulesAux___closed__4;
lean_inc(x_20);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_5);
x_27 = lean_mk_syntax_ident(x_5);
x_28 = l_Array_mkArray2___rarg(x_26, x_27);
x_29 = l_Lean_Elab_Command_elabMacroRulesAux___closed__5;
lean_inc(x_20);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_28);
x_31 = l_Array_mkArray2___rarg(x_3, x_30);
x_32 = l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_31);
x_34 = l_Lean_Elab_Command_getRef(x_7, x_8, x_24);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = l_Lean_Elab_Command_elabMacroRulesAux___closed__56;
x_235 = lean_array_push(x_234, x_33);
x_236 = l_Lean_Elab_Command_elabMacroRulesAux___closed__58;
x_237 = l_Lean_mkSepArray(x_235, x_236);
lean_dec(x_235);
x_35 = x_237;
goto block_233;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_2, 0);
x_239 = l_Lean_Syntax_TSepArray_getElems___rarg(x_238);
x_240 = lean_array_push(x_239, x_33);
x_241 = l_Lean_Elab_Command_elabMacroRulesAux___closed__58;
x_242 = l_Lean_mkSepArray(x_240, x_241);
lean_dec(x_240);
x_35 = x_242;
goto block_233;
}
block_233:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_SourceInfo_fromRef(x_36, x_19);
x_39 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_37);
lean_dec(x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_41);
lean_dec(x_8);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l_Lean_Elab_Command_elabMacroRulesAux___closed__12;
lean_inc(x_38);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
x_48 = l_Array_append___rarg(x_47, x_35);
x_49 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_38);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_48);
x_51 = l_Lean_Elab_Command_elabMacroRulesAux___closed__13;
lean_inc(x_38);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Array_mkArray3___rarg(x_46, x_50, x_52);
x_54 = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
lean_inc(x_38);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_38);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_53);
x_56 = l_Array_mkArray1___rarg(x_55);
lean_inc(x_38);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_38);
lean_ctor_set(x_57, 1, x_49);
lean_ctor_set(x_57, 2, x_56);
x_58 = l_Lean_Elab_Command_elabMacroRulesAux___closed__8;
lean_inc(x_38);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Command_elabMacroRulesAux___closed__16;
lean_inc(x_40);
lean_inc(x_44);
x_61 = l_Lean_addMacroScope(x_44, x_60, x_40);
x_62 = lean_box(0);
x_63 = l_Lean_Elab_Command_elabMacroRulesAux___closed__15;
lean_inc(x_38);
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_38);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_62);
x_65 = 1;
x_66 = l_Lean_mkIdentFrom(x_4, x_5, x_65);
x_67 = l_Array_mkArray2___rarg(x_64, x_66);
lean_inc(x_38);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_38);
lean_ctor_set(x_68, 1, x_49);
lean_ctor_set(x_68, 2, x_67);
x_69 = l_Lean_Elab_Command_elabMacroRulesAux___closed__17;
lean_inc(x_38);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_38);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Elab_Command_elabMacroRulesAux___closed__20;
lean_inc(x_40);
lean_inc(x_44);
x_72 = l_Lean_addMacroScope(x_44, x_71, x_40);
x_73 = l_Lean_Elab_Command_elabMacroRulesAux___closed__19;
x_74 = l_Lean_Elab_Command_elabMacroRulesAux___closed__25;
lean_inc(x_38);
x_75 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_75, 0, x_38);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_74);
x_76 = l_Lean_Elab_Command_elabMacroRulesAux___closed__26;
lean_inc(x_38);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_38);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Command_elabMacroRulesAux___closed__27;
lean_inc(x_38);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_38);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_append___rarg(x_47, x_14);
x_81 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_38);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_38);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Elab_Command_elabMacroRulesAux___closed__33;
lean_inc(x_38);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_38);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Array_mkArray1___rarg(x_84);
x_86 = l_Lean_Elab_Command_elabMacroRulesAux___closed__32;
lean_inc(x_38);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_38);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_85);
x_88 = l_Array_mkArray1___rarg(x_87);
lean_inc(x_38);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_38);
lean_ctor_set(x_89, 1, x_49);
lean_ctor_set(x_89, 2, x_88);
x_90 = l_Array_mkArray1___rarg(x_89);
lean_inc(x_38);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_38);
lean_ctor_set(x_91, 1, x_49);
lean_ctor_set(x_91, 2, x_90);
x_92 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5;
lean_inc(x_38);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_38);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_Elab_Command_elabMacroRulesAux___closed__36;
lean_inc(x_38);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_38);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Elab_Command_elabMacroRulesAux___closed__41;
lean_inc(x_40);
lean_inc(x_44);
x_97 = l_Lean_addMacroScope(x_44, x_96, x_40);
x_98 = l_Lean_Elab_Command_elabMacroRulesAux___closed__40;
x_99 = l_Lean_Elab_Command_elabMacroRulesAux___closed__45;
lean_inc(x_38);
x_100 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_100, 0, x_38);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_99);
x_101 = l_Lean_Elab_Command_elabMacroRulesAux___closed__50;
x_102 = l_Lean_addMacroScope(x_44, x_101, x_40);
x_103 = l_Lean_Elab_Command_elabMacroRulesAux___closed__47;
x_104 = l_Lean_Elab_Command_elabMacroRulesAux___closed__54;
lean_inc(x_38);
x_105 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_105, 0, x_38);
lean_ctor_set(x_105, 1, x_103);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_104);
x_106 = l_Array_mkArray1___rarg(x_105);
lean_inc(x_38);
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_38);
lean_ctor_set(x_107, 1, x_49);
lean_ctor_set(x_107, 2, x_106);
x_108 = l_Array_mkArray2___rarg(x_100, x_107);
x_109 = l_Lean_Elab_Command_elabMacroRulesAux___closed__38;
lean_inc(x_38);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_38);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_108);
x_111 = l_Array_mkArray2___rarg(x_95, x_110);
x_112 = l_Lean_Elab_Command_elabMacroRulesAux___closed__35;
lean_inc(x_38);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_38);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_111);
x_114 = l_Array_mkArray4___rarg(x_82, x_91, x_93, x_113);
x_115 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__5;
lean_inc(x_38);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_38);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_114);
x_117 = lean_array_push(x_80, x_116);
lean_inc(x_38);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_38);
lean_ctor_set(x_118, 1, x_49);
lean_ctor_set(x_118, 2, x_117);
x_119 = l_Array_mkArray1___rarg(x_118);
x_120 = l_Lean_Elab_Command_elabMacroRulesAux___closed__30;
lean_inc(x_38);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_38);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_119);
x_122 = l_Array_mkArray2___rarg(x_79, x_121);
x_123 = l_Lean_Elab_Command_elabMacroRulesAux___closed__28;
lean_inc(x_38);
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_38);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_124, 2, x_122);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = l_Lean_Elab_Command_elabMacroRulesAux___closed__55;
lean_inc(x_38);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_38);
lean_ctor_set(x_126, 1, x_49);
lean_ctor_set(x_126, 2, x_125);
x_127 = l_Array_mkArray8___rarg(x_126, x_57, x_59, x_68, x_70, x_75, x_77, x_124);
x_128 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_38);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_42, 0, x_129);
return x_42;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
lean_dec(x_1);
x_131 = l_Array_mkArray1___rarg(x_130);
x_132 = l_Array_append___rarg(x_47, x_131);
lean_inc(x_38);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_38);
lean_ctor_set(x_133, 1, x_49);
lean_ctor_set(x_133, 2, x_132);
x_134 = l_Array_mkArray8___rarg(x_133, x_57, x_59, x_68, x_70, x_75, x_77, x_124);
x_135 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_38);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_42, 0, x_136);
return x_42;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_137 = lean_ctor_get(x_42, 0);
x_138 = lean_ctor_get(x_42, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_42);
x_139 = l_Lean_Elab_Command_elabMacroRulesAux___closed__12;
lean_inc(x_38);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_38);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
x_142 = l_Array_append___rarg(x_141, x_35);
x_143 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_38);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_38);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_142);
x_145 = l_Lean_Elab_Command_elabMacroRulesAux___closed__13;
lean_inc(x_38);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_38);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Array_mkArray3___rarg(x_140, x_144, x_146);
x_148 = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
lean_inc(x_38);
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_38);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_147);
x_150 = l_Array_mkArray1___rarg(x_149);
lean_inc(x_38);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_38);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_150);
x_152 = l_Lean_Elab_Command_elabMacroRulesAux___closed__8;
lean_inc(x_38);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_38);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_Elab_Command_elabMacroRulesAux___closed__16;
lean_inc(x_40);
lean_inc(x_137);
x_155 = l_Lean_addMacroScope(x_137, x_154, x_40);
x_156 = lean_box(0);
x_157 = l_Lean_Elab_Command_elabMacroRulesAux___closed__15;
lean_inc(x_38);
x_158 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_158, 0, x_38);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_155);
lean_ctor_set(x_158, 3, x_156);
x_159 = 1;
x_160 = l_Lean_mkIdentFrom(x_4, x_5, x_159);
x_161 = l_Array_mkArray2___rarg(x_158, x_160);
lean_inc(x_38);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_38);
lean_ctor_set(x_162, 1, x_143);
lean_ctor_set(x_162, 2, x_161);
x_163 = l_Lean_Elab_Command_elabMacroRulesAux___closed__17;
lean_inc(x_38);
x_164 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_164, 0, x_38);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_Elab_Command_elabMacroRulesAux___closed__20;
lean_inc(x_40);
lean_inc(x_137);
x_166 = l_Lean_addMacroScope(x_137, x_165, x_40);
x_167 = l_Lean_Elab_Command_elabMacroRulesAux___closed__19;
x_168 = l_Lean_Elab_Command_elabMacroRulesAux___closed__25;
lean_inc(x_38);
x_169 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_169, 0, x_38);
lean_ctor_set(x_169, 1, x_167);
lean_ctor_set(x_169, 2, x_166);
lean_ctor_set(x_169, 3, x_168);
x_170 = l_Lean_Elab_Command_elabMacroRulesAux___closed__26;
lean_inc(x_38);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_38);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Lean_Elab_Command_elabMacroRulesAux___closed__27;
lean_inc(x_38);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_38);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Array_append___rarg(x_141, x_14);
x_175 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_38);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_38);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_Elab_Command_elabMacroRulesAux___closed__33;
lean_inc(x_38);
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_38);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Array_mkArray1___rarg(x_178);
x_180 = l_Lean_Elab_Command_elabMacroRulesAux___closed__32;
lean_inc(x_38);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_38);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_181, 2, x_179);
x_182 = l_Array_mkArray1___rarg(x_181);
lean_inc(x_38);
x_183 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_183, 0, x_38);
lean_ctor_set(x_183, 1, x_143);
lean_ctor_set(x_183, 2, x_182);
x_184 = l_Array_mkArray1___rarg(x_183);
lean_inc(x_38);
x_185 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_185, 0, x_38);
lean_ctor_set(x_185, 1, x_143);
lean_ctor_set(x_185, 2, x_184);
x_186 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5;
lean_inc(x_38);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_38);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_Elab_Command_elabMacroRulesAux___closed__36;
lean_inc(x_38);
x_189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_189, 0, x_38);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_Elab_Command_elabMacroRulesAux___closed__41;
lean_inc(x_40);
lean_inc(x_137);
x_191 = l_Lean_addMacroScope(x_137, x_190, x_40);
x_192 = l_Lean_Elab_Command_elabMacroRulesAux___closed__40;
x_193 = l_Lean_Elab_Command_elabMacroRulesAux___closed__45;
lean_inc(x_38);
x_194 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_194, 0, x_38);
lean_ctor_set(x_194, 1, x_192);
lean_ctor_set(x_194, 2, x_191);
lean_ctor_set(x_194, 3, x_193);
x_195 = l_Lean_Elab_Command_elabMacroRulesAux___closed__50;
x_196 = l_Lean_addMacroScope(x_137, x_195, x_40);
x_197 = l_Lean_Elab_Command_elabMacroRulesAux___closed__47;
x_198 = l_Lean_Elab_Command_elabMacroRulesAux___closed__54;
lean_inc(x_38);
x_199 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_199, 0, x_38);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_196);
lean_ctor_set(x_199, 3, x_198);
x_200 = l_Array_mkArray1___rarg(x_199);
lean_inc(x_38);
x_201 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_201, 0, x_38);
lean_ctor_set(x_201, 1, x_143);
lean_ctor_set(x_201, 2, x_200);
x_202 = l_Array_mkArray2___rarg(x_194, x_201);
x_203 = l_Lean_Elab_Command_elabMacroRulesAux___closed__38;
lean_inc(x_38);
x_204 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_204, 0, x_38);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set(x_204, 2, x_202);
x_205 = l_Array_mkArray2___rarg(x_189, x_204);
x_206 = l_Lean_Elab_Command_elabMacroRulesAux___closed__35;
lean_inc(x_38);
x_207 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_207, 0, x_38);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_207, 2, x_205);
x_208 = l_Array_mkArray4___rarg(x_176, x_185, x_187, x_207);
x_209 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__5;
lean_inc(x_38);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_38);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_210, 2, x_208);
x_211 = lean_array_push(x_174, x_210);
lean_inc(x_38);
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_38);
lean_ctor_set(x_212, 1, x_143);
lean_ctor_set(x_212, 2, x_211);
x_213 = l_Array_mkArray1___rarg(x_212);
x_214 = l_Lean_Elab_Command_elabMacroRulesAux___closed__30;
lean_inc(x_38);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_38);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_215, 2, x_213);
x_216 = l_Array_mkArray2___rarg(x_173, x_215);
x_217 = l_Lean_Elab_Command_elabMacroRulesAux___closed__28;
lean_inc(x_38);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_38);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_216);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_219 = l_Lean_Elab_Command_elabMacroRulesAux___closed__55;
lean_inc(x_38);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_38);
lean_ctor_set(x_220, 1, x_143);
lean_ctor_set(x_220, 2, x_219);
x_221 = l_Array_mkArray8___rarg(x_220, x_151, x_153, x_162, x_164, x_169, x_171, x_218);
x_222 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_223 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_223, 0, x_38);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_221);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_138);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_225 = lean_ctor_get(x_1, 0);
lean_inc(x_225);
lean_dec(x_1);
x_226 = l_Array_mkArray1___rarg(x_225);
x_227 = l_Array_append___rarg(x_141, x_226);
lean_inc(x_38);
x_228 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_228, 0, x_38);
lean_ctor_set(x_228, 1, x_143);
lean_ctor_set(x_228, 2, x_227);
x_229 = l_Array_mkArray8___rarg(x_228, x_151, x_153, x_162, x_164, x_169, x_171, x_218);
x_230 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_38);
lean_ctor_set(x_231, 1, x_230);
lean_ctor_set(x_231, 2, x_229);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_138);
return x_232;
}
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_13);
if (x_243 == 0)
{
return x_13;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_13, 0);
x_245 = lean_ctor_get(x_13, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_13);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMacroRulesAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabMacroRulesAux___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMacroRulesAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMacroRulesAux___spec__4(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRulesAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabMacroRulesAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("macro_rules", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("kind", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = l_Lean_Elab_Command_getRef(x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_13, x_15);
x_17 = l_Lean_Elab_Command_getCurrMacroScope(x_9, x_10, x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Command_getMainModule___rarg(x_10, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__1;
lean_inc(x_16);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
x_25 = l_Array_append___rarg(x_24, x_8);
lean_inc(x_1);
lean_inc(x_16);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Array_mkArray1___rarg(x_26);
lean_inc(x_16);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_27);
if (lean_obj_tag(x_6) == 0)
{
x_29 = x_24;
goto block_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_6, 0);
lean_inc(x_77);
lean_dec(x_6);
x_78 = l_Array_mkArray1___rarg(x_77);
x_29 = x_78;
goto block_76;
}
block_76:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Array_append___rarg(x_24, x_29);
lean_inc(x_1);
lean_inc(x_16);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_1);
lean_ctor_set(x_31, 2, x_30);
if (lean_obj_tag(x_5) == 0)
{
x_32 = x_24;
goto block_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_5, 0);
lean_inc(x_65);
lean_dec(x_5);
x_66 = l_Lean_Elab_Command_elabMacroRulesAux___closed__12;
lean_inc(x_16);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_16);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Array_append___rarg(x_24, x_65);
lean_inc(x_1);
lean_inc(x_16);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_16);
lean_ctor_set(x_69, 1, x_1);
lean_ctor_set(x_69, 2, x_68);
x_70 = l_Lean_Elab_Command_elabMacroRulesAux___closed__13;
lean_inc(x_16);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_16);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Array_mkArray3___rarg(x_67, x_69, x_71);
x_73 = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
lean_inc(x_16);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_16);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_72);
x_75 = l_Array_mkArray1___rarg(x_74);
x_32 = x_75;
goto block_64;
}
block_64:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Array_append___rarg(x_24, x_32);
lean_inc(x_1);
lean_inc(x_16);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_1);
lean_ctor_set(x_34, 2, x_33);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_35 = x_57;
goto block_56;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_7);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_7, 0);
x_60 = lean_mk_syntax_ident(x_59);
lean_ctor_set(x_7, 0, x_60);
x_35 = x_7;
goto block_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_7, 0);
lean_inc(x_61);
lean_dec(x_7);
x_62 = lean_mk_syntax_ident(x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_35 = x_63;
goto block_56;
}
}
block_56:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = l_Lean_Elab_Command_elabMacroRulesAux___closed__55;
lean_inc(x_16);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_1);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Array_mkArray6___rarg(x_31, x_34, x_3, x_23, x_37, x_28);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_39, 2, x_38);
if (lean_is_scalar(x_21)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_21;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_20);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec(x_35);
x_42 = l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__2;
lean_inc(x_16);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__3;
lean_inc(x_16);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_16);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Elab_Command_elabMacroRulesAux___closed__26;
lean_inc(x_16);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_16);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__4;
lean_inc(x_16);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_16);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Array_mkArray5___rarg(x_43, x_45, x_47, x_41, x_49);
x_51 = l_Array_append___rarg(x_24, x_50);
lean_inc(x_16);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_16);
lean_ctor_set(x_52, 1, x_1);
lean_ctor_set(x_52, 2, x_51);
x_53 = l_Array_mkArray6___rarg(x_31, x_34, x_3, x_23, x_52, x_28);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_16);
lean_ctor_set(x_54, 1, x_4);
lean_ctor_set(x_54, 2, x_53);
if (lean_is_scalar(x_21)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_21;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_20);
return x_55;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attrKind", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__6;
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("basicFun", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3;
x_4 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__2;
lean_inc(x_10);
x_12 = l_Lean_Syntax_isOfKind(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(4u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
x_19 = l_Lean_Syntax_matchesNull(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_3);
x_20 = lean_unsigned_to_nat(5u);
lean_inc(x_17);
x_21 = l_Lean_Syntax_matchesNull(x_17, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Syntax_getArg(x_17, x_14);
lean_dec(x_17);
x_24 = l_Lean_Syntax_getArg(x_1, x_20);
x_25 = l_Lean_Elab_Command_elabMacroRulesAux___closed__30;
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Syntax_getArg(x_24, x_18);
lean_dec(x_24);
x_29 = lean_unsigned_to_nat(1u);
lean_inc(x_28);
x_30 = l_Lean_Syntax_matchesNull(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_31 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_32 = lean_box(2);
x_33 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_31);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_31);
x_35 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3;
lean_inc(x_15);
x_36 = lean_array_push(x_35, x_15);
x_37 = lean_array_push(x_36, x_34);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_Lean_Syntax_getId(x_23);
lean_dec(x_23);
x_40 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_replaceRef(x_38, x_41);
lean_dec(x_41);
lean_dec(x_38);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_6, 6);
lean_dec(x_45);
lean_ctor_set(x_6, 6, x_43);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Elab_Command_resolveSyntaxKind(x_39, x_6, x_7, x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_47, x_31, x_6, x_7, x_48);
lean_dec(x_5);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_6);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_6, 0);
x_55 = lean_ctor_get(x_6, 1);
x_56 = lean_ctor_get(x_6, 2);
x_57 = lean_ctor_get(x_6, 3);
x_58 = lean_ctor_get(x_6, 4);
x_59 = lean_ctor_get(x_6, 5);
x_60 = lean_ctor_get(x_6, 7);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_6);
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_55);
lean_ctor_set(x_61, 2, x_56);
lean_ctor_set(x_61, 3, x_57);
lean_ctor_set(x_61, 4, x_58);
lean_ctor_set(x_61, 5, x_59);
lean_ctor_set(x_61, 6, x_43);
lean_ctor_set(x_61, 7, x_60);
lean_inc(x_7);
lean_inc(x_61);
x_62 = l_Lean_Elab_Command_resolveSyntaxKind(x_39, x_61, x_7, x_42);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_63, x_31, x_61, x_7, x_64);
lean_dec(x_5);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_61);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_68 = x_62;
} else {
 lean_dec_ref(x_62);
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
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = l_Lean_Syntax_getArg(x_28, x_18);
x_71 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__5;
lean_inc(x_70);
x_72 = l_Lean_Syntax_isOfKind(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_70);
x_73 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_74 = lean_box(2);
x_75 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_73);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_73);
x_77 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3;
lean_inc(x_15);
x_78 = lean_array_push(x_77, x_15);
x_79 = lean_array_push(x_78, x_76);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_75);
lean_ctor_set(x_80, 2, x_79);
x_81 = l_Lean_Syntax_getId(x_23);
lean_dec(x_23);
x_82 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_replaceRef(x_80, x_83);
lean_dec(x_83);
lean_dec(x_80);
x_86 = !lean_is_exclusive(x_6);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_6, 6);
lean_dec(x_87);
lean_ctor_set(x_6, 6, x_85);
lean_inc(x_7);
lean_inc(x_6);
x_88 = l_Lean_Elab_Command_resolveSyntaxKind(x_81, x_6, x_7, x_84);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_89, x_73, x_6, x_7, x_90);
lean_dec(x_5);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_6);
lean_dec(x_73);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
return x_88;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_88);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_6, 0);
x_97 = lean_ctor_get(x_6, 1);
x_98 = lean_ctor_get(x_6, 2);
x_99 = lean_ctor_get(x_6, 3);
x_100 = lean_ctor_get(x_6, 4);
x_101 = lean_ctor_get(x_6, 5);
x_102 = lean_ctor_get(x_6, 7);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_6);
x_103 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_97);
lean_ctor_set(x_103, 2, x_98);
lean_ctor_set(x_103, 3, x_99);
lean_ctor_set(x_103, 4, x_100);
lean_ctor_set(x_103, 5, x_101);
lean_ctor_set(x_103, 6, x_85);
lean_ctor_set(x_103, 7, x_102);
lean_inc(x_7);
lean_inc(x_103);
x_104 = l_Lean_Elab_Command_resolveSyntaxKind(x_81, x_103, x_7, x_84);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_105, x_73, x_103, x_7, x_106);
lean_dec(x_5);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_103);
lean_dec(x_73);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = l_Lean_Syntax_getArg(x_70, x_29);
lean_inc(x_112);
x_113 = l_Lean_Syntax_matchesNull(x_112, x_29);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_112);
lean_dec(x_70);
x_114 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_115 = lean_box(2);
x_116 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_114);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_114);
x_118 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3;
lean_inc(x_15);
x_119 = lean_array_push(x_118, x_15);
x_120 = lean_array_push(x_119, x_117);
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_116);
lean_ctor_set(x_121, 2, x_120);
x_122 = l_Lean_Syntax_getId(x_23);
lean_dec(x_23);
x_123 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_replaceRef(x_121, x_124);
lean_dec(x_124);
lean_dec(x_121);
x_127 = !lean_is_exclusive(x_6);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_6, 6);
lean_dec(x_128);
lean_ctor_set(x_6, 6, x_126);
lean_inc(x_7);
lean_inc(x_6);
x_129 = l_Lean_Elab_Command_resolveSyntaxKind(x_122, x_6, x_7, x_125);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_130, x_114, x_6, x_7, x_131);
lean_dec(x_5);
return x_132;
}
else
{
uint8_t x_133; 
lean_dec(x_6);
lean_dec(x_114);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_133 = !lean_is_exclusive(x_129);
if (x_133 == 0)
{
return x_129;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_129, 0);
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_129);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_137 = lean_ctor_get(x_6, 0);
x_138 = lean_ctor_get(x_6, 1);
x_139 = lean_ctor_get(x_6, 2);
x_140 = lean_ctor_get(x_6, 3);
x_141 = lean_ctor_get(x_6, 4);
x_142 = lean_ctor_get(x_6, 5);
x_143 = lean_ctor_get(x_6, 7);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_6);
x_144 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_144, 0, x_137);
lean_ctor_set(x_144, 1, x_138);
lean_ctor_set(x_144, 2, x_139);
lean_ctor_set(x_144, 3, x_140);
lean_ctor_set(x_144, 4, x_141);
lean_ctor_set(x_144, 5, x_142);
lean_ctor_set(x_144, 6, x_126);
lean_ctor_set(x_144, 7, x_143);
lean_inc(x_7);
lean_inc(x_144);
x_145 = l_Lean_Elab_Command_resolveSyntaxKind(x_122, x_144, x_7, x_125);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_146, x_114, x_144, x_7, x_147);
lean_dec(x_5);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_144);
lean_dec(x_114);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_151 = x_145;
} else {
 lean_dec_ref(x_145);
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
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = l_Lean_Syntax_getArg(x_112, x_18);
lean_dec(x_112);
lean_inc(x_153);
x_154 = l_Lean_Syntax_matchesNull(x_153, x_29);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_153);
lean_dec(x_70);
x_155 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_156 = lean_box(2);
x_157 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_155);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_155);
x_159 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3;
lean_inc(x_15);
x_160 = lean_array_push(x_159, x_15);
x_161 = lean_array_push(x_160, x_158);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_157);
lean_ctor_set(x_162, 2, x_161);
x_163 = l_Lean_Syntax_getId(x_23);
lean_dec(x_23);
x_164 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_replaceRef(x_162, x_165);
lean_dec(x_165);
lean_dec(x_162);
x_168 = !lean_is_exclusive(x_6);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_6, 6);
lean_dec(x_169);
lean_ctor_set(x_6, 6, x_167);
lean_inc(x_7);
lean_inc(x_6);
x_170 = l_Lean_Elab_Command_resolveSyntaxKind(x_163, x_6, x_7, x_166);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_171, x_155, x_6, x_7, x_172);
lean_dec(x_5);
return x_173;
}
else
{
uint8_t x_174; 
lean_dec(x_6);
lean_dec(x_155);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_174 = !lean_is_exclusive(x_170);
if (x_174 == 0)
{
return x_170;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_170, 0);
x_176 = lean_ctor_get(x_170, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_170);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_6, 0);
x_179 = lean_ctor_get(x_6, 1);
x_180 = lean_ctor_get(x_6, 2);
x_181 = lean_ctor_get(x_6, 3);
x_182 = lean_ctor_get(x_6, 4);
x_183 = lean_ctor_get(x_6, 5);
x_184 = lean_ctor_get(x_6, 7);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_6);
x_185 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_185, 0, x_178);
lean_ctor_set(x_185, 1, x_179);
lean_ctor_set(x_185, 2, x_180);
lean_ctor_set(x_185, 3, x_181);
lean_ctor_set(x_185, 4, x_182);
lean_ctor_set(x_185, 5, x_183);
lean_ctor_set(x_185, 6, x_167);
lean_ctor_set(x_185, 7, x_184);
lean_inc(x_7);
lean_inc(x_185);
x_186 = l_Lean_Elab_Command_resolveSyntaxKind(x_163, x_185, x_7, x_166);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_187, x_155, x_185, x_7, x_188);
lean_dec(x_5);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_185);
lean_dec(x_155);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_190 = lean_ctor_get(x_186, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_192 = x_186;
} else {
 lean_dec_ref(x_186);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = l_Lean_Syntax_getArg(x_153, x_18);
lean_dec(x_153);
x_195 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__5;
lean_inc(x_194);
x_196 = l_Lean_Syntax_isOfKind(x_194, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_194);
lean_dec(x_70);
x_197 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_198 = lean_box(2);
x_199 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_197);
x_200 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_197);
x_201 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3;
lean_inc(x_15);
x_202 = lean_array_push(x_201, x_15);
x_203 = lean_array_push(x_202, x_200);
x_204 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_204, 0, x_198);
lean_ctor_set(x_204, 1, x_199);
lean_ctor_set(x_204, 2, x_203);
x_205 = l_Lean_Syntax_getId(x_23);
lean_dec(x_23);
x_206 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = l_Lean_replaceRef(x_204, x_207);
lean_dec(x_207);
lean_dec(x_204);
x_210 = !lean_is_exclusive(x_6);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_6, 6);
lean_dec(x_211);
lean_ctor_set(x_6, 6, x_209);
lean_inc(x_7);
lean_inc(x_6);
x_212 = l_Lean_Elab_Command_resolveSyntaxKind(x_205, x_6, x_7, x_208);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_213, x_197, x_6, x_7, x_214);
lean_dec(x_5);
return x_215;
}
else
{
uint8_t x_216; 
lean_dec(x_6);
lean_dec(x_197);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_216 = !lean_is_exclusive(x_212);
if (x_216 == 0)
{
return x_212;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_212, 0);
x_218 = lean_ctor_get(x_212, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_212);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_220 = lean_ctor_get(x_6, 0);
x_221 = lean_ctor_get(x_6, 1);
x_222 = lean_ctor_get(x_6, 2);
x_223 = lean_ctor_get(x_6, 3);
x_224 = lean_ctor_get(x_6, 4);
x_225 = lean_ctor_get(x_6, 5);
x_226 = lean_ctor_get(x_6, 7);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_6);
x_227 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_227, 0, x_220);
lean_ctor_set(x_227, 1, x_221);
lean_ctor_set(x_227, 2, x_222);
lean_ctor_set(x_227, 3, x_223);
lean_ctor_set(x_227, 4, x_224);
lean_ctor_set(x_227, 5, x_225);
lean_ctor_set(x_227, 6, x_209);
lean_ctor_set(x_227, 7, x_226);
lean_inc(x_7);
lean_inc(x_227);
x_228 = l_Lean_Elab_Command_resolveSyntaxKind(x_205, x_227, x_7, x_208);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = l_Lean_Elab_Command_elabMacroRulesAux(x_2, x_5, x_10, x_15, x_229, x_197, x_227, x_7, x_230);
lean_dec(x_5);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_227);
lean_dec(x_197);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_232 = lean_ctor_get(x_228, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_228, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_234 = x_228;
} else {
 lean_dec_ref(x_228);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
lean_dec(x_28);
x_236 = l_Lean_Syntax_getArg(x_70, x_14);
lean_dec(x_70);
x_237 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3;
lean_inc(x_15);
x_238 = lean_array_push(x_237, x_15);
lean_inc(x_236);
x_239 = lean_array_push(x_238, x_236);
x_240 = lean_box(2);
x_241 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
x_242 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
lean_ctor_set(x_242, 2, x_239);
x_243 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = l_Lean_replaceRef(x_242, x_244);
lean_dec(x_244);
lean_dec(x_242);
x_247 = !lean_is_exclusive(x_6);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_248 = lean_ctor_get(x_6, 6);
lean_dec(x_248);
lean_ctor_set(x_6, 6, x_246);
x_249 = l_Lean_Elab_Command_getRef(x_6, x_7, x_245);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = 0;
x_253 = l_Lean_SourceInfo_fromRef(x_250, x_252);
x_254 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_251);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_255);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_258 = l_Lean_Elab_Command_elabMacroRulesAux___closed__4;
lean_inc(x_253);
x_259 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_259, 0, x_253);
lean_ctor_set(x_259, 1, x_258);
lean_inc(x_23);
x_260 = l_Array_mkArray2___rarg(x_259, x_23);
x_261 = l_Lean_Elab_Command_elabMacroRulesAux___closed__5;
lean_inc(x_253);
x_262 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_262, 0, x_253);
lean_ctor_set(x_262, 1, x_261);
lean_ctor_set(x_262, 2, x_260);
x_263 = l_Array_mkArray2___rarg(x_10, x_262);
x_264 = l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
x_265 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_265, 0, x_253);
lean_ctor_set(x_265, 1, x_264);
lean_ctor_set(x_265, 2, x_263);
x_266 = l_Lean_Elab_Command_getRef(x_6, x_7, x_257);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_388 = l_Lean_Elab_Command_elabMacroRulesAux___closed__56;
x_389 = lean_array_push(x_388, x_265);
x_390 = l_Lean_Elab_Command_elabMacroRulesAux___closed__58;
x_391 = l_Lean_mkSepArray(x_389, x_390);
lean_dec(x_389);
x_267 = x_391;
goto block_387;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_392 = lean_ctor_get(x_5, 0);
lean_inc(x_392);
lean_dec(x_5);
x_393 = l_Lean_Syntax_TSepArray_getElems___rarg(x_392);
lean_dec(x_392);
x_394 = lean_array_push(x_393, x_265);
x_395 = l_Lean_Elab_Command_elabMacroRulesAux___closed__58;
x_396 = l_Lean_mkSepArray(x_394, x_395);
lean_dec(x_394);
x_267 = x_396;
goto block_387;
}
block_387:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_dec(x_266);
x_270 = l_Lean_SourceInfo_fromRef(x_268, x_252);
x_271 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_269);
lean_dec(x_6);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_273);
lean_dec(x_7);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_276 = lean_ctor_get(x_274, 0);
x_277 = l_Lean_Elab_Command_elabMacroRulesAux___closed__12;
lean_inc(x_270);
x_278 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_278, 0, x_270);
lean_ctor_set(x_278, 1, x_277);
x_279 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
x_280 = l_Array_append___rarg(x_279, x_267);
lean_inc(x_270);
x_281 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_281, 0, x_270);
lean_ctor_set(x_281, 1, x_241);
lean_ctor_set(x_281, 2, x_280);
x_282 = l_Lean_Elab_Command_elabMacroRulesAux___closed__13;
lean_inc(x_270);
x_283 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_283, 0, x_270);
lean_ctor_set(x_283, 1, x_282);
x_284 = l_Array_mkArray3___rarg(x_278, x_281, x_283);
x_285 = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
lean_inc(x_270);
x_286 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_286, 0, x_270);
lean_ctor_set(x_286, 1, x_285);
lean_ctor_set(x_286, 2, x_284);
x_287 = l_Array_mkArray1___rarg(x_286);
lean_inc(x_270);
x_288 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_288, 0, x_270);
lean_ctor_set(x_288, 1, x_241);
lean_ctor_set(x_288, 2, x_287);
x_289 = l_Lean_Elab_Command_elabMacroRulesAux___closed__8;
lean_inc(x_270);
x_290 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_290, 0, x_270);
lean_ctor_set(x_290, 1, x_289);
x_291 = l_Lean_Syntax_getId(x_23);
x_292 = 1;
x_293 = l_Lean_mkIdentFrom(x_15, x_291, x_292);
x_294 = l_Array_mkArray2___rarg(x_293, x_23);
lean_inc(x_270);
x_295 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_295, 0, x_270);
lean_ctor_set(x_295, 1, x_241);
lean_ctor_set(x_295, 2, x_294);
x_296 = l_Lean_Elab_Command_elabMacroRulesAux___closed__17;
lean_inc(x_270);
x_297 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_297, 0, x_270);
lean_ctor_set(x_297, 1, x_296);
x_298 = l_Lean_Elab_Command_elabMacroRulesAux___closed__20;
x_299 = l_Lean_addMacroScope(x_276, x_298, x_272);
x_300 = l_Lean_Elab_Command_elabMacroRulesAux___closed__19;
x_301 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__7;
lean_inc(x_270);
x_302 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_302, 0, x_270);
lean_ctor_set(x_302, 1, x_300);
lean_ctor_set(x_302, 2, x_299);
lean_ctor_set(x_302, 3, x_301);
x_303 = l_Lean_Elab_Command_elabMacroRulesAux___closed__26;
lean_inc(x_270);
x_304 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_304, 0, x_270);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Elab_Command_elabMacroRulesAux___closed__27;
lean_inc(x_270);
x_306 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_306, 0, x_270);
lean_ctor_set(x_306, 1, x_305);
x_307 = l_Array_mkArray1___rarg(x_194);
lean_inc(x_270);
x_308 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_308, 0, x_270);
lean_ctor_set(x_308, 1, x_241);
lean_ctor_set(x_308, 2, x_307);
lean_inc(x_270);
x_309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_309, 0, x_270);
lean_ctor_set(x_309, 1, x_241);
lean_ctor_set(x_309, 2, x_279);
x_310 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5;
lean_inc(x_270);
x_311 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_311, 0, x_270);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Array_mkArray4___rarg(x_308, x_309, x_311, x_236);
x_313 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__9;
lean_inc(x_270);
x_314 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_314, 0, x_270);
lean_ctor_set(x_314, 1, x_313);
lean_ctor_set(x_314, 2, x_312);
x_315 = l_Array_mkArray2___rarg(x_306, x_314);
x_316 = l_Lean_Elab_Command_elabMacroRulesAux___closed__28;
lean_inc(x_270);
x_317 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_317, 0, x_270);
lean_ctor_set(x_317, 1, x_316);
lean_ctor_set(x_317, 2, x_315);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_318 = l_Lean_Elab_Command_elabMacroRulesAux___closed__55;
lean_inc(x_270);
x_319 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_319, 0, x_270);
lean_ctor_set(x_319, 1, x_241);
lean_ctor_set(x_319, 2, x_318);
x_320 = l_Array_mkArray8___rarg(x_319, x_288, x_290, x_295, x_297, x_302, x_304, x_317);
x_321 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_322 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_322, 0, x_270);
lean_ctor_set(x_322, 1, x_321);
lean_ctor_set(x_322, 2, x_320);
lean_ctor_set(x_274, 0, x_322);
return x_274;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_323 = lean_ctor_get(x_2, 0);
lean_inc(x_323);
lean_dec(x_2);
x_324 = l_Array_mkArray1___rarg(x_323);
x_325 = l_Array_append___rarg(x_279, x_324);
lean_inc(x_270);
x_326 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_326, 0, x_270);
lean_ctor_set(x_326, 1, x_241);
lean_ctor_set(x_326, 2, x_325);
x_327 = l_Array_mkArray8___rarg(x_326, x_288, x_290, x_295, x_297, x_302, x_304, x_317);
x_328 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_329 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_329, 0, x_270);
lean_ctor_set(x_329, 1, x_328);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_274, 0, x_329);
return x_274;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_330 = lean_ctor_get(x_274, 0);
x_331 = lean_ctor_get(x_274, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_274);
x_332 = l_Lean_Elab_Command_elabMacroRulesAux___closed__12;
lean_inc(x_270);
x_333 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_333, 0, x_270);
lean_ctor_set(x_333, 1, x_332);
x_334 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
x_335 = l_Array_append___rarg(x_334, x_267);
lean_inc(x_270);
x_336 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_336, 0, x_270);
lean_ctor_set(x_336, 1, x_241);
lean_ctor_set(x_336, 2, x_335);
x_337 = l_Lean_Elab_Command_elabMacroRulesAux___closed__13;
lean_inc(x_270);
x_338 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_338, 0, x_270);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Array_mkArray3___rarg(x_333, x_336, x_338);
x_340 = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
lean_inc(x_270);
x_341 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_341, 0, x_270);
lean_ctor_set(x_341, 1, x_340);
lean_ctor_set(x_341, 2, x_339);
x_342 = l_Array_mkArray1___rarg(x_341);
lean_inc(x_270);
x_343 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_343, 0, x_270);
lean_ctor_set(x_343, 1, x_241);
lean_ctor_set(x_343, 2, x_342);
x_344 = l_Lean_Elab_Command_elabMacroRulesAux___closed__8;
lean_inc(x_270);
x_345 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_345, 0, x_270);
lean_ctor_set(x_345, 1, x_344);
x_346 = l_Lean_Syntax_getId(x_23);
x_347 = 1;
x_348 = l_Lean_mkIdentFrom(x_15, x_346, x_347);
x_349 = l_Array_mkArray2___rarg(x_348, x_23);
lean_inc(x_270);
x_350 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_350, 0, x_270);
lean_ctor_set(x_350, 1, x_241);
lean_ctor_set(x_350, 2, x_349);
x_351 = l_Lean_Elab_Command_elabMacroRulesAux___closed__17;
lean_inc(x_270);
x_352 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_352, 0, x_270);
lean_ctor_set(x_352, 1, x_351);
x_353 = l_Lean_Elab_Command_elabMacroRulesAux___closed__20;
x_354 = l_Lean_addMacroScope(x_330, x_353, x_272);
x_355 = l_Lean_Elab_Command_elabMacroRulesAux___closed__19;
x_356 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__7;
lean_inc(x_270);
x_357 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_357, 0, x_270);
lean_ctor_set(x_357, 1, x_355);
lean_ctor_set(x_357, 2, x_354);
lean_ctor_set(x_357, 3, x_356);
x_358 = l_Lean_Elab_Command_elabMacroRulesAux___closed__26;
lean_inc(x_270);
x_359 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_359, 0, x_270);
lean_ctor_set(x_359, 1, x_358);
x_360 = l_Lean_Elab_Command_elabMacroRulesAux___closed__27;
lean_inc(x_270);
x_361 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_361, 0, x_270);
lean_ctor_set(x_361, 1, x_360);
x_362 = l_Array_mkArray1___rarg(x_194);
lean_inc(x_270);
x_363 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_363, 0, x_270);
lean_ctor_set(x_363, 1, x_241);
lean_ctor_set(x_363, 2, x_362);
lean_inc(x_270);
x_364 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_364, 0, x_270);
lean_ctor_set(x_364, 1, x_241);
lean_ctor_set(x_364, 2, x_334);
x_365 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5;
lean_inc(x_270);
x_366 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_366, 0, x_270);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_Array_mkArray4___rarg(x_363, x_364, x_366, x_236);
x_368 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__9;
lean_inc(x_270);
x_369 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_369, 0, x_270);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set(x_369, 2, x_367);
x_370 = l_Array_mkArray2___rarg(x_361, x_369);
x_371 = l_Lean_Elab_Command_elabMacroRulesAux___closed__28;
lean_inc(x_270);
x_372 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_372, 0, x_270);
lean_ctor_set(x_372, 1, x_371);
lean_ctor_set(x_372, 2, x_370);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_373 = l_Lean_Elab_Command_elabMacroRulesAux___closed__55;
lean_inc(x_270);
x_374 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_374, 0, x_270);
lean_ctor_set(x_374, 1, x_241);
lean_ctor_set(x_374, 2, x_373);
x_375 = l_Array_mkArray8___rarg(x_374, x_343, x_345, x_350, x_352, x_357, x_359, x_372);
x_376 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_377 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_377, 0, x_270);
lean_ctor_set(x_377, 1, x_376);
lean_ctor_set(x_377, 2, x_375);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_331);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_379 = lean_ctor_get(x_2, 0);
lean_inc(x_379);
lean_dec(x_2);
x_380 = l_Array_mkArray1___rarg(x_379);
x_381 = l_Array_append___rarg(x_334, x_380);
lean_inc(x_270);
x_382 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_382, 0, x_270);
lean_ctor_set(x_382, 1, x_241);
lean_ctor_set(x_382, 2, x_381);
x_383 = l_Array_mkArray8___rarg(x_382, x_343, x_345, x_350, x_352, x_357, x_359, x_372);
x_384 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_385 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_385, 0, x_270);
lean_ctor_set(x_385, 1, x_384);
lean_ctor_set(x_385, 2, x_383);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_331);
return x_386;
}
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_397 = lean_ctor_get(x_6, 0);
x_398 = lean_ctor_get(x_6, 1);
x_399 = lean_ctor_get(x_6, 2);
x_400 = lean_ctor_get(x_6, 3);
x_401 = lean_ctor_get(x_6, 4);
x_402 = lean_ctor_get(x_6, 5);
x_403 = lean_ctor_get(x_6, 7);
lean_inc(x_403);
lean_inc(x_402);
lean_inc(x_401);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_6);
x_404 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_404, 0, x_397);
lean_ctor_set(x_404, 1, x_398);
lean_ctor_set(x_404, 2, x_399);
lean_ctor_set(x_404, 3, x_400);
lean_ctor_set(x_404, 4, x_401);
lean_ctor_set(x_404, 5, x_402);
lean_ctor_set(x_404, 6, x_246);
lean_ctor_set(x_404, 7, x_403);
x_405 = l_Lean_Elab_Command_getRef(x_404, x_7, x_245);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = 0;
x_409 = l_Lean_SourceInfo_fromRef(x_406, x_408);
x_410 = l_Lean_Elab_Command_getCurrMacroScope(x_404, x_7, x_407);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
x_412 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_411);
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
lean_dec(x_412);
x_414 = l_Lean_Elab_Command_elabMacroRulesAux___closed__4;
lean_inc(x_409);
x_415 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_415, 0, x_409);
lean_ctor_set(x_415, 1, x_414);
lean_inc(x_23);
x_416 = l_Array_mkArray2___rarg(x_415, x_23);
x_417 = l_Lean_Elab_Command_elabMacroRulesAux___closed__5;
lean_inc(x_409);
x_418 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_418, 0, x_409);
lean_ctor_set(x_418, 1, x_417);
lean_ctor_set(x_418, 2, x_416);
x_419 = l_Array_mkArray2___rarg(x_10, x_418);
x_420 = l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
x_421 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_421, 0, x_409);
lean_ctor_set(x_421, 1, x_420);
lean_ctor_set(x_421, 2, x_419);
x_422 = l_Lean_Elab_Command_getRef(x_404, x_7, x_413);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_490 = l_Lean_Elab_Command_elabMacroRulesAux___closed__56;
x_491 = lean_array_push(x_490, x_421);
x_492 = l_Lean_Elab_Command_elabMacroRulesAux___closed__58;
x_493 = l_Lean_mkSepArray(x_491, x_492);
lean_dec(x_491);
x_423 = x_493;
goto block_489;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_494 = lean_ctor_get(x_5, 0);
lean_inc(x_494);
lean_dec(x_5);
x_495 = l_Lean_Syntax_TSepArray_getElems___rarg(x_494);
lean_dec(x_494);
x_496 = lean_array_push(x_495, x_421);
x_497 = l_Lean_Elab_Command_elabMacroRulesAux___closed__58;
x_498 = l_Lean_mkSepArray(x_496, x_497);
lean_dec(x_496);
x_423 = x_498;
goto block_489;
}
block_489:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_dec(x_422);
x_426 = l_Lean_SourceInfo_fromRef(x_424, x_408);
x_427 = l_Lean_Elab_Command_getCurrMacroScope(x_404, x_7, x_425);
lean_dec(x_404);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_429);
lean_dec(x_7);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_433 = x_430;
} else {
 lean_dec_ref(x_430);
 x_433 = lean_box(0);
}
x_434 = l_Lean_Elab_Command_elabMacroRulesAux___closed__12;
lean_inc(x_426);
x_435 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_435, 0, x_426);
lean_ctor_set(x_435, 1, x_434);
x_436 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4;
x_437 = l_Array_append___rarg(x_436, x_423);
lean_inc(x_426);
x_438 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_438, 0, x_426);
lean_ctor_set(x_438, 1, x_241);
lean_ctor_set(x_438, 2, x_437);
x_439 = l_Lean_Elab_Command_elabMacroRulesAux___closed__13;
lean_inc(x_426);
x_440 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_440, 0, x_426);
lean_ctor_set(x_440, 1, x_439);
x_441 = l_Array_mkArray3___rarg(x_435, x_438, x_440);
x_442 = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
lean_inc(x_426);
x_443 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_443, 0, x_426);
lean_ctor_set(x_443, 1, x_442);
lean_ctor_set(x_443, 2, x_441);
x_444 = l_Array_mkArray1___rarg(x_443);
lean_inc(x_426);
x_445 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_445, 0, x_426);
lean_ctor_set(x_445, 1, x_241);
lean_ctor_set(x_445, 2, x_444);
x_446 = l_Lean_Elab_Command_elabMacroRulesAux___closed__8;
lean_inc(x_426);
x_447 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_447, 0, x_426);
lean_ctor_set(x_447, 1, x_446);
x_448 = l_Lean_Syntax_getId(x_23);
x_449 = 1;
x_450 = l_Lean_mkIdentFrom(x_15, x_448, x_449);
x_451 = l_Array_mkArray2___rarg(x_450, x_23);
lean_inc(x_426);
x_452 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_452, 0, x_426);
lean_ctor_set(x_452, 1, x_241);
lean_ctor_set(x_452, 2, x_451);
x_453 = l_Lean_Elab_Command_elabMacroRulesAux___closed__17;
lean_inc(x_426);
x_454 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_454, 0, x_426);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_Lean_Elab_Command_elabMacroRulesAux___closed__20;
x_456 = l_Lean_addMacroScope(x_431, x_455, x_428);
x_457 = l_Lean_Elab_Command_elabMacroRulesAux___closed__19;
x_458 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__7;
lean_inc(x_426);
x_459 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_459, 0, x_426);
lean_ctor_set(x_459, 1, x_457);
lean_ctor_set(x_459, 2, x_456);
lean_ctor_set(x_459, 3, x_458);
x_460 = l_Lean_Elab_Command_elabMacroRulesAux___closed__26;
lean_inc(x_426);
x_461 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_461, 0, x_426);
lean_ctor_set(x_461, 1, x_460);
x_462 = l_Lean_Elab_Command_elabMacroRulesAux___closed__27;
lean_inc(x_426);
x_463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_463, 0, x_426);
lean_ctor_set(x_463, 1, x_462);
x_464 = l_Array_mkArray1___rarg(x_194);
lean_inc(x_426);
x_465 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_465, 0, x_426);
lean_ctor_set(x_465, 1, x_241);
lean_ctor_set(x_465, 2, x_464);
lean_inc(x_426);
x_466 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_466, 0, x_426);
lean_ctor_set(x_466, 1, x_241);
lean_ctor_set(x_466, 2, x_436);
x_467 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5;
lean_inc(x_426);
x_468 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_468, 0, x_426);
lean_ctor_set(x_468, 1, x_467);
x_469 = l_Array_mkArray4___rarg(x_465, x_466, x_468, x_236);
x_470 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__9;
lean_inc(x_426);
x_471 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_471, 0, x_426);
lean_ctor_set(x_471, 1, x_470);
lean_ctor_set(x_471, 2, x_469);
x_472 = l_Array_mkArray2___rarg(x_463, x_471);
x_473 = l_Lean_Elab_Command_elabMacroRulesAux___closed__28;
lean_inc(x_426);
x_474 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_474, 0, x_426);
lean_ctor_set(x_474, 1, x_473);
lean_ctor_set(x_474, 2, x_472);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_475 = l_Lean_Elab_Command_elabMacroRulesAux___closed__55;
lean_inc(x_426);
x_476 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_476, 0, x_426);
lean_ctor_set(x_476, 1, x_241);
lean_ctor_set(x_476, 2, x_475);
x_477 = l_Array_mkArray8___rarg(x_476, x_445, x_447, x_452, x_454, x_459, x_461, x_474);
x_478 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_479 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_479, 0, x_426);
lean_ctor_set(x_479, 1, x_478);
lean_ctor_set(x_479, 2, x_477);
if (lean_is_scalar(x_433)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_433;
}
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_432);
return x_480;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_481 = lean_ctor_get(x_2, 0);
lean_inc(x_481);
lean_dec(x_2);
x_482 = l_Array_mkArray1___rarg(x_481);
x_483 = l_Array_append___rarg(x_436, x_482);
lean_inc(x_426);
x_484 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_484, 0, x_426);
lean_ctor_set(x_484, 1, x_241);
lean_ctor_set(x_484, 2, x_483);
x_485 = l_Array_mkArray8___rarg(x_484, x_445, x_447, x_452, x_454, x_459, x_461, x_474);
x_486 = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
x_487 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_487, 0, x_426);
lean_ctor_set(x_487, 1, x_486);
lean_ctor_set(x_487, 2, x_485);
if (lean_is_scalar(x_433)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_433;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_432);
return x_488;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; 
lean_dec(x_17);
x_499 = lean_unsigned_to_nat(5u);
x_500 = l_Lean_Syntax_getArg(x_1, x_499);
x_501 = l_Lean_Elab_Command_elabMacroRulesAux___closed__30;
lean_inc(x_500);
x_502 = l_Lean_Syntax_isOfKind(x_500, x_501);
if (x_502 == 0)
{
lean_object* x_503; 
lean_dec(x_500);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_503 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(x_8);
return x_503;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_504 = l_Lean_Syntax_getArg(x_500, x_18);
lean_dec(x_500);
x_505 = l_Lean_Syntax_getArgs(x_504);
lean_dec(x_504);
x_506 = lean_box(2);
x_507 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_505);
x_508 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
lean_ctor_set(x_508, 2, x_505);
x_509 = l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3;
x_510 = lean_array_push(x_509, x_15);
x_511 = lean_array_push(x_510, x_508);
x_512 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_512, 0, x_506);
lean_ctor_set(x_512, 1, x_507);
lean_ctor_set(x_512, 2, x_511);
x_513 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lambda__1___boxed), 11, 6);
lean_closure_set(x_513, 0, x_507);
lean_closure_set(x_513, 1, x_501);
lean_closure_set(x_513, 2, x_10);
lean_closure_set(x_513, 3, x_3);
lean_closure_set(x_513, 4, x_5);
lean_closure_set(x_513, 5, x_2);
x_514 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
x_517 = l_Lean_replaceRef(x_512, x_515);
lean_dec(x_515);
lean_dec(x_512);
x_518 = !lean_is_exclusive(x_6);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_6, 6);
lean_dec(x_519);
lean_ctor_set(x_6, 6, x_517);
x_520 = l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__1;
x_521 = l_Lean_Elab_Command_expandNoKindMacroRulesAux(x_505, x_520, x_513, x_6, x_7, x_516);
if (lean_obj_tag(x_521) == 0)
{
uint8_t x_522; 
x_522 = !lean_is_exclusive(x_521);
if (x_522 == 0)
{
return x_521;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_521, 0);
x_524 = lean_ctor_get(x_521, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_521);
x_525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
}
else
{
uint8_t x_526; 
x_526 = !lean_is_exclusive(x_521);
if (x_526 == 0)
{
return x_521;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_521, 0);
x_528 = lean_ctor_get(x_521, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_521);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_527);
lean_ctor_set(x_529, 1, x_528);
return x_529;
}
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_530 = lean_ctor_get(x_6, 0);
x_531 = lean_ctor_get(x_6, 1);
x_532 = lean_ctor_get(x_6, 2);
x_533 = lean_ctor_get(x_6, 3);
x_534 = lean_ctor_get(x_6, 4);
x_535 = lean_ctor_get(x_6, 5);
x_536 = lean_ctor_get(x_6, 7);
lean_inc(x_536);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_532);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_6);
x_537 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_537, 0, x_530);
lean_ctor_set(x_537, 1, x_531);
lean_ctor_set(x_537, 2, x_532);
lean_ctor_set(x_537, 3, x_533);
lean_ctor_set(x_537, 4, x_534);
lean_ctor_set(x_537, 5, x_535);
lean_ctor_set(x_537, 6, x_517);
lean_ctor_set(x_537, 7, x_536);
x_538 = l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__1;
x_539 = l_Lean_Elab_Command_expandNoKindMacroRulesAux(x_505, x_538, x_513, x_537, x_7, x_516);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_542 = x_539;
} else {
 lean_dec_ref(x_539);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_544 = lean_ctor_get(x_539, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_539, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_546 = x_539;
} else {
 lean_dec_ref(x_539);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc(x_9);
x_11 = l_Lean_Syntax_matchesNull(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_9, x_13);
lean_dec(x_9);
x_15 = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_Syntax_getArg(x_14, x_8);
lean_dec(x_14);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Command_elabMacroRules___lambda__2(x_1, x_4, x_2, x_21, x_20, x_5, x_6, x_7);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Command_elabMacroRules___lambda__2(x_1, x_4, x_2, x_24, x_23, x_5, x_6, x_7);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Lean_Elab_Command_elabMacroRulesAux___closed__7;
x_4 = l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("docComment", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2;
x_3 = l_Lean_Elab_Command_elabMacroRulesAux___closed__7;
x_4 = l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__1;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_12 = l_Lean_Syntax_matchesNull(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_15 = l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__3;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__18___rarg(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Command_elabMacroRules___lambda__3(x_1, x_5, x_19, x_18, x_2, x_3, x_4);
lean_dec(x_1);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Command_elabMacroRules___lambda__3(x_1, x_5, x_22, x_21, x_2, x_3, x_4);
lean_dec(x_1);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabMacroRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules___lambda__4), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Command_elabMacroRules___closed__1;
x_6 = l_Lean_Elab_Command_adaptExpander(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabMacroRules___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabMacroRules___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabMacroRules___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabMacroRules___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabMacroRules", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1;
x_2 = l_Lean_Elab_Command_elabMacroRulesAux___closed__6;
x_3 = l_Lean_Elab_Command_elabMacroRulesAux___closed__7;
x_4 = l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMacroRules), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__3;
x_3 = l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(67u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__1;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__2;
x_4 = lean_unsigned_to_nat(32u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__4;
x_2 = lean_unsigned_to_nat(40u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__5;
x_4 = lean_unsigned_to_nat(54u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_MacroRules(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabMacroRulesAux___spec__1___rarg___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__6);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__7 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__7);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__8 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__8();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__8);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__9 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__9();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__9);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__10 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__10();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__10);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__11 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__11();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__11);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__12 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__12();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__12);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__13 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__13();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__13);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__14 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__14();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__14);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__15 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__15();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__15);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__16 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__16();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___lambda__2___closed__16);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabMacroRulesAux___spec__5___closed__5);
l_Lean_Elab_Command_elabMacroRulesAux___closed__1 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__1);
l_Lean_Elab_Command_elabMacroRulesAux___closed__2 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__2);
l_Lean_Elab_Command_elabMacroRulesAux___closed__3 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__3);
l_Lean_Elab_Command_elabMacroRulesAux___closed__4 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__4);
l_Lean_Elab_Command_elabMacroRulesAux___closed__5 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__5);
l_Lean_Elab_Command_elabMacroRulesAux___closed__6 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__6);
l_Lean_Elab_Command_elabMacroRulesAux___closed__7 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__7);
l_Lean_Elab_Command_elabMacroRulesAux___closed__8 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__8);
l_Lean_Elab_Command_elabMacroRulesAux___closed__9 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__9);
l_Lean_Elab_Command_elabMacroRulesAux___closed__10 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__10);
l_Lean_Elab_Command_elabMacroRulesAux___closed__11 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__11);
l_Lean_Elab_Command_elabMacroRulesAux___closed__12 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__12);
l_Lean_Elab_Command_elabMacroRulesAux___closed__13 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__13);
l_Lean_Elab_Command_elabMacroRulesAux___closed__14 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__14);
l_Lean_Elab_Command_elabMacroRulesAux___closed__15 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__15);
l_Lean_Elab_Command_elabMacroRulesAux___closed__16 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__16);
l_Lean_Elab_Command_elabMacroRulesAux___closed__17 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__17);
l_Lean_Elab_Command_elabMacroRulesAux___closed__18 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__18);
l_Lean_Elab_Command_elabMacroRulesAux___closed__19 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__19);
l_Lean_Elab_Command_elabMacroRulesAux___closed__20 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__20();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__20);
l_Lean_Elab_Command_elabMacroRulesAux___closed__21 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__21();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__21);
l_Lean_Elab_Command_elabMacroRulesAux___closed__22 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__22();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__22);
l_Lean_Elab_Command_elabMacroRulesAux___closed__23 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__23();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__23);
l_Lean_Elab_Command_elabMacroRulesAux___closed__24 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__24();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__24);
l_Lean_Elab_Command_elabMacroRulesAux___closed__25 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__25();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__25);
l_Lean_Elab_Command_elabMacroRulesAux___closed__26 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__26);
l_Lean_Elab_Command_elabMacroRulesAux___closed__27 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__27();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__27);
l_Lean_Elab_Command_elabMacroRulesAux___closed__28 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__28();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__28);
l_Lean_Elab_Command_elabMacroRulesAux___closed__29 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__29();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__29);
l_Lean_Elab_Command_elabMacroRulesAux___closed__30 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__30();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__30);
l_Lean_Elab_Command_elabMacroRulesAux___closed__31 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__31();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__31);
l_Lean_Elab_Command_elabMacroRulesAux___closed__32 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__32();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__32);
l_Lean_Elab_Command_elabMacroRulesAux___closed__33 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__33();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__33);
l_Lean_Elab_Command_elabMacroRulesAux___closed__34 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__34();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__34);
l_Lean_Elab_Command_elabMacroRulesAux___closed__35 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__35();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__35);
l_Lean_Elab_Command_elabMacroRulesAux___closed__36 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__36();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__36);
l_Lean_Elab_Command_elabMacroRulesAux___closed__37 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__37();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__37);
l_Lean_Elab_Command_elabMacroRulesAux___closed__38 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__38();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__38);
l_Lean_Elab_Command_elabMacroRulesAux___closed__39 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__39();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__39);
l_Lean_Elab_Command_elabMacroRulesAux___closed__40 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__40();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__40);
l_Lean_Elab_Command_elabMacroRulesAux___closed__41 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__41();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__41);
l_Lean_Elab_Command_elabMacroRulesAux___closed__42 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__42();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__42);
l_Lean_Elab_Command_elabMacroRulesAux___closed__43 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__43();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__43);
l_Lean_Elab_Command_elabMacroRulesAux___closed__44 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__44();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__44);
l_Lean_Elab_Command_elabMacroRulesAux___closed__45 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__45();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__45);
l_Lean_Elab_Command_elabMacroRulesAux___closed__46 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__46();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__46);
l_Lean_Elab_Command_elabMacroRulesAux___closed__47 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__47();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__47);
l_Lean_Elab_Command_elabMacroRulesAux___closed__48 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__48();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__48);
l_Lean_Elab_Command_elabMacroRulesAux___closed__49 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__49();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__49);
l_Lean_Elab_Command_elabMacroRulesAux___closed__50 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__50();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__50);
l_Lean_Elab_Command_elabMacroRulesAux___closed__51 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__51();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__51);
l_Lean_Elab_Command_elabMacroRulesAux___closed__52 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__52();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__52);
l_Lean_Elab_Command_elabMacroRulesAux___closed__53 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__53();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__53);
l_Lean_Elab_Command_elabMacroRulesAux___closed__54 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__54();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__54);
l_Lean_Elab_Command_elabMacroRulesAux___closed__55 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__55();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__55);
l_Lean_Elab_Command_elabMacroRulesAux___closed__56 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__56();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__56);
l_Lean_Elab_Command_elabMacroRulesAux___closed__57 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__57();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__57);
l_Lean_Elab_Command_elabMacroRulesAux___closed__58 = _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__58();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRulesAux___closed__58);
l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__1);
l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__2);
l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__3);
l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__1___closed__4);
l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__1);
l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__2 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__2);
l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__3);
l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__4 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__4);
l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__5 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__5);
l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__6 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__6);
l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__7 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__7);
l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__8 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__8);
l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__9 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__2___closed__9);
l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__1 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__1);
l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__2 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__2);
l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__3 = _init_l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___lambda__4___closed__3);
l_Lean_Elab_Command_elabMacroRules___closed__1 = _init_l_Lean_Elab_Command_elabMacroRules___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMacroRules___closed__1);
l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__1);
l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__2);
l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__3);
l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules___closed__4);
res = l___regBuiltin_Lean_Elab_Command_elabMacroRules(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
