// Lean compiler output
// Module: Lean.Elab.ElabRules
// Imports: Init Lean.Elab.MacroArgUtil Lean.Elab.AuxDef
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
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__6;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2;
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__5;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__3;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabElabRulesAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElab(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
static lean_object* l_Lean_Elab_Command_elabElab___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__8;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74;
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__12;
static lean_object* l_Lean_Elab_Command_elabElab___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
static lean_object* l_Lean_Elab_Command_elabElab___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab___closed__2;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9;
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
static lean_object* l_Lean_Elab_Command_elabElabRules___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__11;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__15;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__4;
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__10;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__5;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__5;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Elab_Command_withExpectedType___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__16;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabElabRulesAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__3;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
static lean_object* l_Lean_Elab_Command_withExpectedType___closed__2;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__10;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
lean_object* l_Array_unzip___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__6;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
extern lean_object* l_Lean_instInhabitedSyntax;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__1;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__13;
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5;
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__7;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__2;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__7;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__1;
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__7;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__1;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabElabRulesAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__14;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77;
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_synthesizeInst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4;
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113;
static lean_object* l_Lean_Elab_Command_elabElab___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__2;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__8;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElab___closed__3;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__9;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
static lean_object* _init_l_Lean_Elab_Command_withExpectedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected type must be known", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_withExpectedType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_withExpectedType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_withExpectedType___closed__2;
x_13 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_synthesizeInst___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_8(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabElabRulesAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabElabRulesAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_3, x_4, x_8);
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
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("|", 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=>", 2);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("choice", 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid elab_rules alternative, unexpected syntax node kind '", 61);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__14() {
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid elab_rules alternative, expected syntax node kind '", 59);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_Syntax_getQuotContent(x_1);
lean_inc(x_11);
x_12 = l_Lean_Syntax_getKind(x_11);
x_13 = l_Lean_Elab_Command_checkRuleKind(x_12, x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__9;
x_15 = lean_name_eq(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__11;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__13;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabElabRulesAux___spec__2(x_6, x_20, x_8, x_9, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
x_22 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__14;
x_27 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__4(x_5, x_26, x_22, x_24, x_25, x_26);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_29, 0, x_5);
x_30 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__16;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__13;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabElabRulesAux___spec__2(x_6, x_33, x_8, x_9, x_10);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_unsigned_to_nat(1u);
x_37 = l_Lean_Syntax_setArg(x_1, x_36, x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_set(x_2, x_38, x_37);
x_40 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_8, x_9, x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Command_getCurrMacroScope(x_8, x_9, x_42);
lean_dec(x_8);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Elab_Command_getMainModule___rarg(x_9, x_44);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_41);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_51 = l_Array_append___rarg(x_50, x_39);
x_52 = lean_box(2);
x_53 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_51);
x_55 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_56 = lean_array_push(x_55, x_54);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_56);
x_58 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_41);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_61 = lean_array_push(x_60, x_49);
x_62 = lean_array_push(x_61, x_57);
x_63 = lean_array_push(x_62, x_59);
x_64 = lean_array_push(x_63, x_3);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_4);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_45, 0, x_65);
return x_45;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_dec(x_45);
x_67 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_41);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_41);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_70 = l_Array_append___rarg(x_69, x_39);
x_71 = lean_box(2);
x_72 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_70);
x_74 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_75 = lean_array_push(x_74, x_73);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_75);
x_77 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_41);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_80 = lean_array_push(x_79, x_68);
x_81 = lean_array_push(x_80, x_76);
x_82 = lean_array_push(x_81, x_78);
x_83 = lean_array_push(x_82, x_3);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_71);
lean_ctor_set(x_84, 1, x_4);
lean_ctor_set(x_84, 2, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_66);
return x_85;
}
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_6);
lean_ctor_set(x_86, 1, x_10);
return x_86;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlt", 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
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
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg(x_7);
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
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg(x_7);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = l_Lean_Syntax_getArg(x_21, x_11);
lean_dec(x_21);
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Syntax_getArg(x_10, x_29);
x_31 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_32 = l_Lean_instInhabitedSyntax;
x_33 = lean_array_get(x_32, x_31, x_11);
x_34 = l_Lean_Syntax_isQuot(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg(x_7);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_41 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2(x_33, x_31, x_30, x_13, x_1, x_10, x_40, x_5, x_6, x_7);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = 1;
x_45 = lean_usize_add(x_3, x_44);
x_46 = lean_array_uset(x_12, x_3, x_42);
x_3 = x_45;
x_4 = x_46;
x_7 = x_43;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_mkIdentFrom(x_7, x_1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_mkIdentFrom(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unsupported syntax category '", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__2;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("aux_def", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attributes", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("@[", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attrInstance", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Attr", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simple", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabRules", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Tactic.Tactic", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fun", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchAlts", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("throwUnsupportedSyntax", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("commandElab", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Command.CommandElab", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CommandElab", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("termElab", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Term.TermElab", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("TermElab", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("basicFun", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stx", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("match", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("matchDiscr", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("syntax category '", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' does not support expected type specification", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expectedType?", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Command.withExpectedType", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("withExpectedType", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
x_11 = lean_name_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4;
x_13 = lean_name_eq(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6;
x_15 = lean_name_eq(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_6);
x_17 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__13;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_20, x_7, x_8, x_9);
lean_dec(x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_6);
lean_inc(x_2);
x_22 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(x_2, x_7, x_8, x_9);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_7, x_8, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_30);
lean_dec(x_8);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_26);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_29);
lean_inc(x_33);
x_36 = l_Lean_addMacroScope(x_33, x_14, x_29);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25;
lean_inc(x_26);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_37);
x_40 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_41 = lean_array_push(x_40, x_23);
x_42 = lean_box(2);
x_43 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_41);
x_45 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_46 = lean_array_push(x_45, x_39);
x_47 = lean_array_push(x_46, x_44);
x_48 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_47);
x_50 = lean_array_push(x_45, x_3);
x_51 = lean_array_push(x_50, x_49);
x_52 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_51);
x_54 = lean_array_push(x_40, x_53);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_43);
lean_ctor_set(x_55, 2, x_54);
x_56 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
lean_inc(x_26);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_26);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_59 = lean_array_push(x_58, x_35);
x_60 = lean_array_push(x_59, x_55);
x_61 = lean_array_push(x_60, x_57);
x_62 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_42);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_61);
x_64 = lean_array_push(x_40, x_63);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_42);
lean_ctor_set(x_65, 1, x_43);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_26);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_26);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_29);
lean_inc(x_33);
x_69 = l_Lean_addMacroScope(x_33, x_68, x_29);
x_70 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_26);
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_26);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_37);
x_72 = lean_mk_syntax_ident(x_2);
x_73 = lean_array_push(x_45, x_71);
x_74 = lean_array_push(x_73, x_72);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_42);
lean_ctor_set(x_75, 1, x_43);
lean_ctor_set(x_75, 2, x_74);
x_76 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_26);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_26);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_29);
lean_inc(x_33);
x_79 = l_Lean_addMacroScope(x_33, x_78, x_29);
x_80 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36;
x_81 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41;
lean_inc(x_26);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_26);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_81);
x_83 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_26);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_26);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_26);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_26);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_88 = l_Array_append___rarg(x_87, x_4);
x_89 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_26);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_26);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_26);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_26);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_array_push(x_40, x_92);
x_94 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_42);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_93);
x_96 = lean_array_push(x_40, x_95);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_42);
lean_ctor_set(x_97, 1, x_43);
lean_ctor_set(x_97, 2, x_96);
x_98 = lean_array_push(x_40, x_97);
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_42);
lean_ctor_set(x_99, 1, x_43);
lean_ctor_set(x_99, 2, x_98);
x_100 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
lean_inc(x_26);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_26);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_103 = l_Lean_addMacroScope(x_33, x_102, x_29);
x_104 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_105 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
x_106 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_106, 0, x_26);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set(x_106, 3, x_105);
x_107 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_108 = lean_array_push(x_107, x_90);
x_109 = lean_array_push(x_108, x_99);
x_110 = lean_array_push(x_109, x_101);
x_111 = lean_array_push(x_110, x_106);
x_112 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_42);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_111);
x_114 = lean_array_push(x_88, x_113);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_42);
lean_ctor_set(x_115, 1, x_43);
lean_ctor_set(x_115, 2, x_114);
x_116 = lean_array_push(x_40, x_115);
x_117 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_42);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_116);
x_119 = lean_array_push(x_45, x_86);
x_120 = lean_array_push(x_119, x_118);
x_121 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_42);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_122, 2, x_120);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_123 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_124 = lean_array_push(x_123, x_65);
x_125 = lean_array_push(x_124, x_67);
x_126 = lean_array_push(x_125, x_75);
x_127 = lean_array_push(x_126, x_77);
x_128 = lean_array_push(x_127, x_82);
x_129 = lean_array_push(x_128, x_84);
x_130 = lean_array_push(x_129, x_122);
x_131 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_31, 0, x_132);
return x_31;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_133 = lean_ctor_get(x_5, 0);
lean_inc(x_133);
lean_dec(x_5);
x_134 = lean_array_push(x_40, x_133);
x_135 = l_Array_append___rarg(x_87, x_134);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_42);
lean_ctor_set(x_136, 1, x_43);
lean_ctor_set(x_136, 2, x_135);
x_137 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_138 = lean_array_push(x_137, x_136);
x_139 = lean_array_push(x_138, x_65);
x_140 = lean_array_push(x_139, x_67);
x_141 = lean_array_push(x_140, x_75);
x_142 = lean_array_push(x_141, x_77);
x_143 = lean_array_push(x_142, x_82);
x_144 = lean_array_push(x_143, x_84);
x_145 = lean_array_push(x_144, x_122);
x_146 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_42);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_145);
lean_ctor_set(x_31, 0, x_147);
return x_31;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_148 = lean_ctor_get(x_31, 0);
x_149 = lean_ctor_get(x_31, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_31);
x_150 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_26);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_26);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_29);
lean_inc(x_148);
x_152 = l_Lean_addMacroScope(x_148, x_14, x_29);
x_153 = lean_box(0);
x_154 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25;
lean_inc(x_26);
x_155 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_155, 0, x_26);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_155, 2, x_152);
lean_ctor_set(x_155, 3, x_153);
x_156 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_157 = lean_array_push(x_156, x_23);
x_158 = lean_box(2);
x_159 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_160, 2, x_157);
x_161 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_162 = lean_array_push(x_161, x_155);
x_163 = lean_array_push(x_162, x_160);
x_164 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_158);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_163);
x_166 = lean_array_push(x_161, x_3);
x_167 = lean_array_push(x_166, x_165);
x_168 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_158);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_167);
x_170 = lean_array_push(x_156, x_169);
x_171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_171, 0, x_158);
lean_ctor_set(x_171, 1, x_159);
lean_ctor_set(x_171, 2, x_170);
x_172 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
lean_inc(x_26);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_26);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_175 = lean_array_push(x_174, x_151);
x_176 = lean_array_push(x_175, x_171);
x_177 = lean_array_push(x_176, x_173);
x_178 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_158);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_179, 2, x_177);
x_180 = lean_array_push(x_156, x_179);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_158);
lean_ctor_set(x_181, 1, x_159);
lean_ctor_set(x_181, 2, x_180);
x_182 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_26);
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_26);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_29);
lean_inc(x_148);
x_185 = l_Lean_addMacroScope(x_148, x_184, x_29);
x_186 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_26);
x_187 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_187, 0, x_26);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_187, 2, x_185);
lean_ctor_set(x_187, 3, x_153);
x_188 = lean_mk_syntax_ident(x_2);
x_189 = lean_array_push(x_161, x_187);
x_190 = lean_array_push(x_189, x_188);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_158);
lean_ctor_set(x_191, 1, x_159);
lean_ctor_set(x_191, 2, x_190);
x_192 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_26);
x_193 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_193, 0, x_26);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_29);
lean_inc(x_148);
x_195 = l_Lean_addMacroScope(x_148, x_194, x_29);
x_196 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36;
x_197 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41;
lean_inc(x_26);
x_198 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_198, 0, x_26);
lean_ctor_set(x_198, 1, x_196);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_197);
x_199 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_26);
x_200 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_200, 0, x_26);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_26);
x_202 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_202, 0, x_26);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_204 = l_Array_append___rarg(x_203, x_4);
x_205 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_26);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_26);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_26);
x_208 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_208, 0, x_26);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_array_push(x_156, x_208);
x_210 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_158);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_211, 2, x_209);
x_212 = lean_array_push(x_156, x_211);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_158);
lean_ctor_set(x_213, 1, x_159);
lean_ctor_set(x_213, 2, x_212);
x_214 = lean_array_push(x_156, x_213);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_158);
lean_ctor_set(x_215, 1, x_159);
lean_ctor_set(x_215, 2, x_214);
x_216 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
lean_inc(x_26);
x_217 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_217, 0, x_26);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_219 = l_Lean_addMacroScope(x_148, x_218, x_29);
x_220 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_221 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
x_222 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_222, 0, x_26);
lean_ctor_set(x_222, 1, x_220);
lean_ctor_set(x_222, 2, x_219);
lean_ctor_set(x_222, 3, x_221);
x_223 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_224 = lean_array_push(x_223, x_206);
x_225 = lean_array_push(x_224, x_215);
x_226 = lean_array_push(x_225, x_217);
x_227 = lean_array_push(x_226, x_222);
x_228 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
x_229 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_229, 0, x_158);
lean_ctor_set(x_229, 1, x_228);
lean_ctor_set(x_229, 2, x_227);
x_230 = lean_array_push(x_204, x_229);
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_158);
lean_ctor_set(x_231, 1, x_159);
lean_ctor_set(x_231, 2, x_230);
x_232 = lean_array_push(x_156, x_231);
x_233 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_234 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_234, 0, x_158);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set(x_234, 2, x_232);
x_235 = lean_array_push(x_161, x_202);
x_236 = lean_array_push(x_235, x_234);
x_237 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_238 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_238, 0, x_158);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_238, 2, x_236);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_239 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_240 = lean_array_push(x_239, x_181);
x_241 = lean_array_push(x_240, x_183);
x_242 = lean_array_push(x_241, x_191);
x_243 = lean_array_push(x_242, x_193);
x_244 = lean_array_push(x_243, x_198);
x_245 = lean_array_push(x_244, x_200);
x_246 = lean_array_push(x_245, x_238);
x_247 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_248 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_248, 0, x_158);
lean_ctor_set(x_248, 1, x_247);
lean_ctor_set(x_248, 2, x_246);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_149);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_250 = lean_ctor_get(x_5, 0);
lean_inc(x_250);
lean_dec(x_5);
x_251 = lean_array_push(x_156, x_250);
x_252 = l_Array_append___rarg(x_203, x_251);
x_253 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_253, 0, x_158);
lean_ctor_set(x_253, 1, x_159);
lean_ctor_set(x_253, 2, x_252);
x_254 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_255 = lean_array_push(x_254, x_253);
x_256 = lean_array_push(x_255, x_181);
x_257 = lean_array_push(x_256, x_183);
x_258 = lean_array_push(x_257, x_191);
x_259 = lean_array_push(x_258, x_193);
x_260 = lean_array_push(x_259, x_198);
x_261 = lean_array_push(x_260, x_200);
x_262 = lean_array_push(x_261, x_238);
x_263 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_264 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_264, 0, x_158);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_262);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_149);
return x_265;
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
lean_dec(x_6);
lean_inc(x_2);
x_266 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(x_2, x_7, x_8, x_9);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_7, x_8, x_268);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_271);
lean_dec(x_7);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_274);
lean_dec(x_8);
x_276 = !lean_is_exclusive(x_275);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_277 = lean_ctor_get(x_275, 0);
x_278 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_270);
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_270);
lean_ctor_set(x_279, 1, x_278);
x_280 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
lean_inc(x_273);
lean_inc(x_277);
x_281 = l_Lean_addMacroScope(x_277, x_280, x_273);
x_282 = lean_box(0);
x_283 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
lean_inc(x_270);
x_284 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_284, 0, x_270);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_281);
lean_ctor_set(x_284, 3, x_282);
x_285 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_286 = lean_array_push(x_285, x_267);
x_287 = lean_box(2);
x_288 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_289 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
lean_ctor_set(x_289, 2, x_286);
x_290 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_291 = lean_array_push(x_290, x_284);
x_292 = lean_array_push(x_291, x_289);
x_293 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_294 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_294, 0, x_287);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set(x_294, 2, x_292);
x_295 = lean_array_push(x_290, x_3);
x_296 = lean_array_push(x_295, x_294);
x_297 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_298 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_298, 0, x_287);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set(x_298, 2, x_296);
x_299 = lean_array_push(x_285, x_298);
x_300 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_300, 0, x_287);
lean_ctor_set(x_300, 1, x_288);
lean_ctor_set(x_300, 2, x_299);
x_301 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
lean_inc(x_270);
x_302 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_302, 0, x_270);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_304 = lean_array_push(x_303, x_279);
x_305 = lean_array_push(x_304, x_300);
x_306 = lean_array_push(x_305, x_302);
x_307 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_308 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_308, 0, x_287);
lean_ctor_set(x_308, 1, x_307);
lean_ctor_set(x_308, 2, x_306);
x_309 = lean_array_push(x_285, x_308);
x_310 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_310, 0, x_287);
lean_ctor_set(x_310, 1, x_288);
lean_ctor_set(x_310, 2, x_309);
x_311 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_270);
x_312 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_312, 0, x_270);
lean_ctor_set(x_312, 1, x_311);
x_313 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_273);
lean_inc(x_277);
x_314 = l_Lean_addMacroScope(x_277, x_313, x_273);
x_315 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_270);
x_316 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_316, 0, x_270);
lean_ctor_set(x_316, 1, x_315);
lean_ctor_set(x_316, 2, x_314);
lean_ctor_set(x_316, 3, x_282);
x_317 = lean_mk_syntax_ident(x_2);
x_318 = lean_array_push(x_290, x_316);
x_319 = lean_array_push(x_318, x_317);
x_320 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_320, 0, x_287);
lean_ctor_set(x_320, 1, x_288);
lean_ctor_set(x_320, 2, x_319);
x_321 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_270);
x_322 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_322, 0, x_270);
lean_ctor_set(x_322, 1, x_321);
x_323 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69;
lean_inc(x_273);
lean_inc(x_277);
x_324 = l_Lean_addMacroScope(x_277, x_323, x_273);
x_325 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_326 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71;
lean_inc(x_270);
x_327 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_327, 0, x_270);
lean_ctor_set(x_327, 1, x_325);
lean_ctor_set(x_327, 2, x_324);
lean_ctor_set(x_327, 3, x_326);
x_328 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_270);
x_329 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_329, 0, x_270);
lean_ctor_set(x_329, 1, x_328);
x_330 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_270);
x_331 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_331, 0, x_270);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_333 = l_Array_append___rarg(x_332, x_4);
x_334 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_270);
x_335 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_335, 0, x_270);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_270);
x_337 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_337, 0, x_270);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_array_push(x_285, x_337);
x_339 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
x_340 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_340, 0, x_287);
lean_ctor_set(x_340, 1, x_339);
lean_ctor_set(x_340, 2, x_338);
x_341 = lean_array_push(x_285, x_340);
x_342 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_342, 0, x_287);
lean_ctor_set(x_342, 1, x_288);
lean_ctor_set(x_342, 2, x_341);
x_343 = lean_array_push(x_285, x_342);
x_344 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_344, 0, x_287);
lean_ctor_set(x_344, 1, x_288);
lean_ctor_set(x_344, 2, x_343);
x_345 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
lean_inc(x_270);
x_346 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_346, 0, x_270);
lean_ctor_set(x_346, 1, x_345);
x_347 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_348 = l_Lean_addMacroScope(x_277, x_347, x_273);
x_349 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_350 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
x_351 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_351, 0, x_270);
lean_ctor_set(x_351, 1, x_349);
lean_ctor_set(x_351, 2, x_348);
lean_ctor_set(x_351, 3, x_350);
x_352 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_353 = lean_array_push(x_352, x_335);
x_354 = lean_array_push(x_353, x_344);
x_355 = lean_array_push(x_354, x_346);
x_356 = lean_array_push(x_355, x_351);
x_357 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
x_358 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_358, 0, x_287);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set(x_358, 2, x_356);
x_359 = lean_array_push(x_333, x_358);
x_360 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_360, 0, x_287);
lean_ctor_set(x_360, 1, x_288);
lean_ctor_set(x_360, 2, x_359);
x_361 = lean_array_push(x_285, x_360);
x_362 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_363 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_363, 0, x_287);
lean_ctor_set(x_363, 1, x_362);
lean_ctor_set(x_363, 2, x_361);
x_364 = lean_array_push(x_290, x_331);
x_365 = lean_array_push(x_364, x_363);
x_366 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_367 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_367, 0, x_287);
lean_ctor_set(x_367, 1, x_366);
lean_ctor_set(x_367, 2, x_365);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_368 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_369 = lean_array_push(x_368, x_310);
x_370 = lean_array_push(x_369, x_312);
x_371 = lean_array_push(x_370, x_320);
x_372 = lean_array_push(x_371, x_322);
x_373 = lean_array_push(x_372, x_327);
x_374 = lean_array_push(x_373, x_329);
x_375 = lean_array_push(x_374, x_367);
x_376 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_377 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_377, 0, x_287);
lean_ctor_set(x_377, 1, x_376);
lean_ctor_set(x_377, 2, x_375);
lean_ctor_set(x_275, 0, x_377);
return x_275;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_378 = lean_ctor_get(x_5, 0);
lean_inc(x_378);
lean_dec(x_5);
x_379 = lean_array_push(x_285, x_378);
x_380 = l_Array_append___rarg(x_332, x_379);
x_381 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_381, 0, x_287);
lean_ctor_set(x_381, 1, x_288);
lean_ctor_set(x_381, 2, x_380);
x_382 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_383 = lean_array_push(x_382, x_381);
x_384 = lean_array_push(x_383, x_310);
x_385 = lean_array_push(x_384, x_312);
x_386 = lean_array_push(x_385, x_320);
x_387 = lean_array_push(x_386, x_322);
x_388 = lean_array_push(x_387, x_327);
x_389 = lean_array_push(x_388, x_329);
x_390 = lean_array_push(x_389, x_367);
x_391 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_392 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_392, 0, x_287);
lean_ctor_set(x_392, 1, x_391);
lean_ctor_set(x_392, 2, x_390);
lean_ctor_set(x_275, 0, x_392);
return x_275;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_393 = lean_ctor_get(x_275, 0);
x_394 = lean_ctor_get(x_275, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_275);
x_395 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_270);
x_396 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_396, 0, x_270);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
lean_inc(x_273);
lean_inc(x_393);
x_398 = l_Lean_addMacroScope(x_393, x_397, x_273);
x_399 = lean_box(0);
x_400 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
lean_inc(x_270);
x_401 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_401, 0, x_270);
lean_ctor_set(x_401, 1, x_400);
lean_ctor_set(x_401, 2, x_398);
lean_ctor_set(x_401, 3, x_399);
x_402 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_403 = lean_array_push(x_402, x_267);
x_404 = lean_box(2);
x_405 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_406 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set(x_406, 2, x_403);
x_407 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_408 = lean_array_push(x_407, x_401);
x_409 = lean_array_push(x_408, x_406);
x_410 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_411 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_411, 0, x_404);
lean_ctor_set(x_411, 1, x_410);
lean_ctor_set(x_411, 2, x_409);
x_412 = lean_array_push(x_407, x_3);
x_413 = lean_array_push(x_412, x_411);
x_414 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_415 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_415, 0, x_404);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set(x_415, 2, x_413);
x_416 = lean_array_push(x_402, x_415);
x_417 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_417, 0, x_404);
lean_ctor_set(x_417, 1, x_405);
lean_ctor_set(x_417, 2, x_416);
x_418 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
lean_inc(x_270);
x_419 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_419, 0, x_270);
lean_ctor_set(x_419, 1, x_418);
x_420 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_421 = lean_array_push(x_420, x_396);
x_422 = lean_array_push(x_421, x_417);
x_423 = lean_array_push(x_422, x_419);
x_424 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_425 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_425, 0, x_404);
lean_ctor_set(x_425, 1, x_424);
lean_ctor_set(x_425, 2, x_423);
x_426 = lean_array_push(x_402, x_425);
x_427 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_427, 0, x_404);
lean_ctor_set(x_427, 1, x_405);
lean_ctor_set(x_427, 2, x_426);
x_428 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_270);
x_429 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_429, 0, x_270);
lean_ctor_set(x_429, 1, x_428);
x_430 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_273);
lean_inc(x_393);
x_431 = l_Lean_addMacroScope(x_393, x_430, x_273);
x_432 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_270);
x_433 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_433, 0, x_270);
lean_ctor_set(x_433, 1, x_432);
lean_ctor_set(x_433, 2, x_431);
lean_ctor_set(x_433, 3, x_399);
x_434 = lean_mk_syntax_ident(x_2);
x_435 = lean_array_push(x_407, x_433);
x_436 = lean_array_push(x_435, x_434);
x_437 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_437, 0, x_404);
lean_ctor_set(x_437, 1, x_405);
lean_ctor_set(x_437, 2, x_436);
x_438 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_270);
x_439 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_439, 0, x_270);
lean_ctor_set(x_439, 1, x_438);
x_440 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69;
lean_inc(x_273);
lean_inc(x_393);
x_441 = l_Lean_addMacroScope(x_393, x_440, x_273);
x_442 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_443 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71;
lean_inc(x_270);
x_444 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_444, 0, x_270);
lean_ctor_set(x_444, 1, x_442);
lean_ctor_set(x_444, 2, x_441);
lean_ctor_set(x_444, 3, x_443);
x_445 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_270);
x_446 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_446, 0, x_270);
lean_ctor_set(x_446, 1, x_445);
x_447 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_270);
x_448 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_448, 0, x_270);
lean_ctor_set(x_448, 1, x_447);
x_449 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_450 = l_Array_append___rarg(x_449, x_4);
x_451 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_270);
x_452 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_452, 0, x_270);
lean_ctor_set(x_452, 1, x_451);
x_453 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_270);
x_454 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_454, 0, x_270);
lean_ctor_set(x_454, 1, x_453);
x_455 = lean_array_push(x_402, x_454);
x_456 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
x_457 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_457, 0, x_404);
lean_ctor_set(x_457, 1, x_456);
lean_ctor_set(x_457, 2, x_455);
x_458 = lean_array_push(x_402, x_457);
x_459 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_459, 0, x_404);
lean_ctor_set(x_459, 1, x_405);
lean_ctor_set(x_459, 2, x_458);
x_460 = lean_array_push(x_402, x_459);
x_461 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_461, 0, x_404);
lean_ctor_set(x_461, 1, x_405);
lean_ctor_set(x_461, 2, x_460);
x_462 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
lean_inc(x_270);
x_463 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_463, 0, x_270);
lean_ctor_set(x_463, 1, x_462);
x_464 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_465 = l_Lean_addMacroScope(x_393, x_464, x_273);
x_466 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_467 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
x_468 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_468, 0, x_270);
lean_ctor_set(x_468, 1, x_466);
lean_ctor_set(x_468, 2, x_465);
lean_ctor_set(x_468, 3, x_467);
x_469 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_470 = lean_array_push(x_469, x_452);
x_471 = lean_array_push(x_470, x_461);
x_472 = lean_array_push(x_471, x_463);
x_473 = lean_array_push(x_472, x_468);
x_474 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
x_475 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_475, 0, x_404);
lean_ctor_set(x_475, 1, x_474);
lean_ctor_set(x_475, 2, x_473);
x_476 = lean_array_push(x_450, x_475);
x_477 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_477, 0, x_404);
lean_ctor_set(x_477, 1, x_405);
lean_ctor_set(x_477, 2, x_476);
x_478 = lean_array_push(x_402, x_477);
x_479 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_480 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_480, 0, x_404);
lean_ctor_set(x_480, 1, x_479);
lean_ctor_set(x_480, 2, x_478);
x_481 = lean_array_push(x_407, x_448);
x_482 = lean_array_push(x_481, x_480);
x_483 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_484 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_484, 0, x_404);
lean_ctor_set(x_484, 1, x_483);
lean_ctor_set(x_484, 2, x_482);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_485 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_486 = lean_array_push(x_485, x_427);
x_487 = lean_array_push(x_486, x_429);
x_488 = lean_array_push(x_487, x_437);
x_489 = lean_array_push(x_488, x_439);
x_490 = lean_array_push(x_489, x_444);
x_491 = lean_array_push(x_490, x_446);
x_492 = lean_array_push(x_491, x_484);
x_493 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_494 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_494, 0, x_404);
lean_ctor_set(x_494, 1, x_493);
lean_ctor_set(x_494, 2, x_492);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_394);
return x_495;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_496 = lean_ctor_get(x_5, 0);
lean_inc(x_496);
lean_dec(x_5);
x_497 = lean_array_push(x_402, x_496);
x_498 = l_Array_append___rarg(x_449, x_497);
x_499 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_499, 0, x_404);
lean_ctor_set(x_499, 1, x_405);
lean_ctor_set(x_499, 2, x_498);
x_500 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_501 = lean_array_push(x_500, x_499);
x_502 = lean_array_push(x_501, x_427);
x_503 = lean_array_push(x_502, x_429);
x_504 = lean_array_push(x_503, x_437);
x_505 = lean_array_push(x_504, x_439);
x_506 = lean_array_push(x_505, x_444);
x_507 = lean_array_push(x_506, x_446);
x_508 = lean_array_push(x_507, x_484);
x_509 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_510 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_510, 0, x_404);
lean_ctor_set(x_510, 1, x_509);
lean_ctor_set(x_510, 2, x_508);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_394);
return x_511;
}
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
lean_dec(x_6);
lean_inc(x_2);
x_512 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(x_2, x_7, x_8, x_9);
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_7, x_8, x_514);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_517);
lean_dec(x_7);
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_520);
lean_dec(x_8);
x_522 = !lean_is_exclusive(x_521);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_523 = lean_ctor_get(x_521, 0);
x_524 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_516);
x_525 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_525, 0, x_516);
lean_ctor_set(x_525, 1, x_524);
x_526 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
lean_inc(x_519);
lean_inc(x_523);
x_527 = l_Lean_addMacroScope(x_523, x_526, x_519);
x_528 = lean_box(0);
x_529 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74;
lean_inc(x_516);
x_530 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_530, 0, x_516);
lean_ctor_set(x_530, 1, x_529);
lean_ctor_set(x_530, 2, x_527);
lean_ctor_set(x_530, 3, x_528);
x_531 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_532 = lean_array_push(x_531, x_513);
x_533 = lean_box(2);
x_534 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_535 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set(x_535, 1, x_534);
lean_ctor_set(x_535, 2, x_532);
x_536 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_537 = lean_array_push(x_536, x_530);
x_538 = lean_array_push(x_537, x_535);
x_539 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_540 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_540, 0, x_533);
lean_ctor_set(x_540, 1, x_539);
lean_ctor_set(x_540, 2, x_538);
x_541 = lean_array_push(x_536, x_3);
x_542 = lean_array_push(x_541, x_540);
x_543 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_544 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_544, 0, x_533);
lean_ctor_set(x_544, 1, x_543);
lean_ctor_set(x_544, 2, x_542);
x_545 = lean_array_push(x_531, x_544);
x_546 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_546, 0, x_533);
lean_ctor_set(x_546, 1, x_534);
lean_ctor_set(x_546, 2, x_545);
x_547 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
lean_inc(x_516);
x_548 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_548, 0, x_516);
lean_ctor_set(x_548, 1, x_547);
x_549 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_550 = lean_array_push(x_549, x_525);
x_551 = lean_array_push(x_550, x_546);
x_552 = lean_array_push(x_551, x_548);
x_553 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_554 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_554, 0, x_533);
lean_ctor_set(x_554, 1, x_553);
lean_ctor_set(x_554, 2, x_552);
x_555 = lean_array_push(x_531, x_554);
x_556 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_556, 0, x_533);
lean_ctor_set(x_556, 1, x_534);
lean_ctor_set(x_556, 2, x_555);
x_557 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_516);
x_558 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_558, 0, x_516);
lean_ctor_set(x_558, 1, x_557);
x_559 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_519);
lean_inc(x_523);
x_560 = l_Lean_addMacroScope(x_523, x_559, x_519);
x_561 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_516);
x_562 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_562, 0, x_516);
lean_ctor_set(x_562, 1, x_561);
lean_ctor_set(x_562, 2, x_560);
lean_ctor_set(x_562, 3, x_528);
x_563 = lean_mk_syntax_ident(x_2);
x_564 = lean_array_push(x_536, x_562);
x_565 = lean_array_push(x_564, x_563);
x_566 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_566, 0, x_533);
lean_ctor_set(x_566, 1, x_534);
lean_ctor_set(x_566, 2, x_565);
x_567 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_516);
x_568 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_568, 0, x_516);
lean_ctor_set(x_568, 1, x_567);
x_569 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
lean_inc(x_519);
lean_inc(x_523);
x_570 = l_Lean_addMacroScope(x_523, x_569, x_519);
x_571 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78;
x_572 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83;
lean_inc(x_516);
x_573 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_573, 0, x_516);
lean_ctor_set(x_573, 1, x_571);
lean_ctor_set(x_573, 2, x_570);
lean_ctor_set(x_573, 3, x_572);
x_574 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_516);
x_575 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_575, 0, x_516);
lean_ctor_set(x_575, 1, x_574);
x_576 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_516);
x_577 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_577, 0, x_516);
lean_ctor_set(x_577, 1, x_576);
x_578 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_inc(x_519);
lean_inc(x_523);
x_579 = l_Lean_addMacroScope(x_523, x_578, x_519);
x_580 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
lean_inc(x_516);
x_581 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_581, 0, x_516);
lean_ctor_set(x_581, 1, x_580);
lean_ctor_set(x_581, 2, x_579);
lean_ctor_set(x_581, 3, x_528);
x_582 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_516);
x_583 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_583, 0, x_516);
lean_ctor_set(x_583, 1, x_582);
x_584 = lean_array_push(x_531, x_583);
x_585 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
x_586 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_586, 0, x_533);
lean_ctor_set(x_586, 1, x_585);
lean_ctor_set(x_586, 2, x_584);
lean_inc(x_581);
x_587 = lean_array_push(x_536, x_581);
lean_inc(x_586);
x_588 = lean_array_push(x_587, x_586);
x_589 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_589, 0, x_533);
lean_ctor_set(x_589, 1, x_534);
lean_ctor_set(x_589, 2, x_588);
x_590 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
lean_inc(x_516);
x_591 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_591, 0, x_516);
lean_ctor_set(x_591, 1, x_590);
x_592 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
lean_inc(x_516);
x_593 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_593, 0, x_516);
lean_ctor_set(x_593, 1, x_592);
x_594 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
x_595 = lean_array_push(x_594, x_581);
x_596 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94;
x_597 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_597, 0, x_533);
lean_ctor_set(x_597, 1, x_596);
lean_ctor_set(x_597, 2, x_595);
x_598 = lean_array_push(x_531, x_597);
x_599 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_599, 0, x_533);
lean_ctor_set(x_599, 1, x_534);
lean_ctor_set(x_599, 2, x_598);
x_600 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
lean_inc(x_516);
x_601 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_601, 0, x_516);
lean_ctor_set(x_601, 1, x_600);
x_602 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_603 = l_Array_append___rarg(x_602, x_4);
x_604 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_516);
x_605 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_605, 0, x_516);
lean_ctor_set(x_605, 1, x_604);
x_606 = lean_array_push(x_531, x_586);
x_607 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_607, 0, x_533);
lean_ctor_set(x_607, 1, x_534);
lean_ctor_set(x_607, 2, x_606);
x_608 = lean_array_push(x_531, x_607);
x_609 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_609, 0, x_533);
lean_ctor_set(x_609, 1, x_534);
lean_ctor_set(x_609, 2, x_608);
x_610 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_611 = l_Lean_addMacroScope(x_523, x_610, x_519);
x_612 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_613 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
x_614 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_614, 0, x_516);
lean_ctor_set(x_614, 1, x_612);
lean_ctor_set(x_614, 2, x_611);
lean_ctor_set(x_614, 3, x_613);
x_615 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_616 = lean_array_push(x_615, x_605);
x_617 = lean_array_push(x_616, x_609);
lean_inc(x_591);
x_618 = lean_array_push(x_617, x_591);
x_619 = lean_array_push(x_618, x_614);
x_620 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
x_621 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_621, 0, x_533);
lean_ctor_set(x_621, 1, x_620);
lean_ctor_set(x_621, 2, x_619);
x_622 = lean_array_push(x_603, x_621);
x_623 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_623, 0, x_533);
lean_ctor_set(x_623, 1, x_534);
lean_ctor_set(x_623, 2, x_622);
x_624 = lean_array_push(x_531, x_623);
x_625 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_626 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_626, 0, x_533);
lean_ctor_set(x_626, 1, x_625);
lean_ctor_set(x_626, 2, x_624);
x_627 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
x_628 = lean_array_push(x_627, x_593);
x_629 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
x_630 = lean_array_push(x_628, x_629);
x_631 = lean_array_push(x_630, x_629);
x_632 = lean_array_push(x_631, x_599);
x_633 = lean_array_push(x_632, x_601);
x_634 = lean_array_push(x_633, x_626);
x_635 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_636 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_636, 0, x_533);
lean_ctor_set(x_636, 1, x_635);
lean_ctor_set(x_636, 2, x_634);
x_637 = lean_array_push(x_615, x_589);
x_638 = lean_array_push(x_637, x_629);
x_639 = lean_array_push(x_638, x_591);
x_640 = lean_array_push(x_639, x_636);
x_641 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
x_642 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_642, 0, x_533);
lean_ctor_set(x_642, 1, x_641);
lean_ctor_set(x_642, 2, x_640);
x_643 = lean_array_push(x_536, x_577);
x_644 = lean_array_push(x_643, x_642);
x_645 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_646 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_646, 0, x_533);
lean_ctor_set(x_646, 1, x_645);
lean_ctor_set(x_646, 2, x_644);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_647 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_648 = lean_array_push(x_647, x_556);
x_649 = lean_array_push(x_648, x_558);
x_650 = lean_array_push(x_649, x_566);
x_651 = lean_array_push(x_650, x_568);
x_652 = lean_array_push(x_651, x_573);
x_653 = lean_array_push(x_652, x_575);
x_654 = lean_array_push(x_653, x_646);
x_655 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_656 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_656, 0, x_533);
lean_ctor_set(x_656, 1, x_655);
lean_ctor_set(x_656, 2, x_654);
lean_ctor_set(x_521, 0, x_656);
return x_521;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_657 = lean_ctor_get(x_5, 0);
lean_inc(x_657);
lean_dec(x_5);
x_658 = lean_array_push(x_531, x_657);
x_659 = l_Array_append___rarg(x_602, x_658);
x_660 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_660, 0, x_533);
lean_ctor_set(x_660, 1, x_534);
lean_ctor_set(x_660, 2, x_659);
x_661 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_662 = lean_array_push(x_661, x_660);
x_663 = lean_array_push(x_662, x_556);
x_664 = lean_array_push(x_663, x_558);
x_665 = lean_array_push(x_664, x_566);
x_666 = lean_array_push(x_665, x_568);
x_667 = lean_array_push(x_666, x_573);
x_668 = lean_array_push(x_667, x_575);
x_669 = lean_array_push(x_668, x_646);
x_670 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_671 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_671, 0, x_533);
lean_ctor_set(x_671, 1, x_670);
lean_ctor_set(x_671, 2, x_669);
lean_ctor_set(x_521, 0, x_671);
return x_521;
}
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_672 = lean_ctor_get(x_521, 0);
x_673 = lean_ctor_get(x_521, 1);
lean_inc(x_673);
lean_inc(x_672);
lean_dec(x_521);
x_674 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_516);
x_675 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_675, 0, x_516);
lean_ctor_set(x_675, 1, x_674);
x_676 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
lean_inc(x_519);
lean_inc(x_672);
x_677 = l_Lean_addMacroScope(x_672, x_676, x_519);
x_678 = lean_box(0);
x_679 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74;
lean_inc(x_516);
x_680 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_680, 0, x_516);
lean_ctor_set(x_680, 1, x_679);
lean_ctor_set(x_680, 2, x_677);
lean_ctor_set(x_680, 3, x_678);
x_681 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_682 = lean_array_push(x_681, x_513);
x_683 = lean_box(2);
x_684 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_685 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_685, 0, x_683);
lean_ctor_set(x_685, 1, x_684);
lean_ctor_set(x_685, 2, x_682);
x_686 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_687 = lean_array_push(x_686, x_680);
x_688 = lean_array_push(x_687, x_685);
x_689 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_690 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_690, 0, x_683);
lean_ctor_set(x_690, 1, x_689);
lean_ctor_set(x_690, 2, x_688);
x_691 = lean_array_push(x_686, x_3);
x_692 = lean_array_push(x_691, x_690);
x_693 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_694 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_694, 0, x_683);
lean_ctor_set(x_694, 1, x_693);
lean_ctor_set(x_694, 2, x_692);
x_695 = lean_array_push(x_681, x_694);
x_696 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_696, 0, x_683);
lean_ctor_set(x_696, 1, x_684);
lean_ctor_set(x_696, 2, x_695);
x_697 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
lean_inc(x_516);
x_698 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_698, 0, x_516);
lean_ctor_set(x_698, 1, x_697);
x_699 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_700 = lean_array_push(x_699, x_675);
x_701 = lean_array_push(x_700, x_696);
x_702 = lean_array_push(x_701, x_698);
x_703 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_704 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_704, 0, x_683);
lean_ctor_set(x_704, 1, x_703);
lean_ctor_set(x_704, 2, x_702);
x_705 = lean_array_push(x_681, x_704);
x_706 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_706, 0, x_683);
lean_ctor_set(x_706, 1, x_684);
lean_ctor_set(x_706, 2, x_705);
x_707 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_516);
x_708 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_708, 0, x_516);
lean_ctor_set(x_708, 1, x_707);
x_709 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_519);
lean_inc(x_672);
x_710 = l_Lean_addMacroScope(x_672, x_709, x_519);
x_711 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_516);
x_712 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_712, 0, x_516);
lean_ctor_set(x_712, 1, x_711);
lean_ctor_set(x_712, 2, x_710);
lean_ctor_set(x_712, 3, x_678);
x_713 = lean_mk_syntax_ident(x_2);
x_714 = lean_array_push(x_686, x_712);
x_715 = lean_array_push(x_714, x_713);
x_716 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_716, 0, x_683);
lean_ctor_set(x_716, 1, x_684);
lean_ctor_set(x_716, 2, x_715);
x_717 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_516);
x_718 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_718, 0, x_516);
lean_ctor_set(x_718, 1, x_717);
x_719 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
lean_inc(x_519);
lean_inc(x_672);
x_720 = l_Lean_addMacroScope(x_672, x_719, x_519);
x_721 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78;
x_722 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83;
lean_inc(x_516);
x_723 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_723, 0, x_516);
lean_ctor_set(x_723, 1, x_721);
lean_ctor_set(x_723, 2, x_720);
lean_ctor_set(x_723, 3, x_722);
x_724 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_516);
x_725 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_725, 0, x_516);
lean_ctor_set(x_725, 1, x_724);
x_726 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_516);
x_727 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_727, 0, x_516);
lean_ctor_set(x_727, 1, x_726);
x_728 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_inc(x_519);
lean_inc(x_672);
x_729 = l_Lean_addMacroScope(x_672, x_728, x_519);
x_730 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
lean_inc(x_516);
x_731 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_731, 0, x_516);
lean_ctor_set(x_731, 1, x_730);
lean_ctor_set(x_731, 2, x_729);
lean_ctor_set(x_731, 3, x_678);
x_732 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_516);
x_733 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_733, 0, x_516);
lean_ctor_set(x_733, 1, x_732);
x_734 = lean_array_push(x_681, x_733);
x_735 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
x_736 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_736, 0, x_683);
lean_ctor_set(x_736, 1, x_735);
lean_ctor_set(x_736, 2, x_734);
lean_inc(x_731);
x_737 = lean_array_push(x_686, x_731);
lean_inc(x_736);
x_738 = lean_array_push(x_737, x_736);
x_739 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_739, 0, x_683);
lean_ctor_set(x_739, 1, x_684);
lean_ctor_set(x_739, 2, x_738);
x_740 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
lean_inc(x_516);
x_741 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_741, 0, x_516);
lean_ctor_set(x_741, 1, x_740);
x_742 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
lean_inc(x_516);
x_743 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_743, 0, x_516);
lean_ctor_set(x_743, 1, x_742);
x_744 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
x_745 = lean_array_push(x_744, x_731);
x_746 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94;
x_747 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_747, 0, x_683);
lean_ctor_set(x_747, 1, x_746);
lean_ctor_set(x_747, 2, x_745);
x_748 = lean_array_push(x_681, x_747);
x_749 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_749, 0, x_683);
lean_ctor_set(x_749, 1, x_684);
lean_ctor_set(x_749, 2, x_748);
x_750 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
lean_inc(x_516);
x_751 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_751, 0, x_516);
lean_ctor_set(x_751, 1, x_750);
x_752 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_753 = l_Array_append___rarg(x_752, x_4);
x_754 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_516);
x_755 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_755, 0, x_516);
lean_ctor_set(x_755, 1, x_754);
x_756 = lean_array_push(x_681, x_736);
x_757 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_757, 0, x_683);
lean_ctor_set(x_757, 1, x_684);
lean_ctor_set(x_757, 2, x_756);
x_758 = lean_array_push(x_681, x_757);
x_759 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_759, 0, x_683);
lean_ctor_set(x_759, 1, x_684);
lean_ctor_set(x_759, 2, x_758);
x_760 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_761 = l_Lean_addMacroScope(x_672, x_760, x_519);
x_762 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_763 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
x_764 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_764, 0, x_516);
lean_ctor_set(x_764, 1, x_762);
lean_ctor_set(x_764, 2, x_761);
lean_ctor_set(x_764, 3, x_763);
x_765 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_766 = lean_array_push(x_765, x_755);
x_767 = lean_array_push(x_766, x_759);
lean_inc(x_741);
x_768 = lean_array_push(x_767, x_741);
x_769 = lean_array_push(x_768, x_764);
x_770 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
x_771 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_771, 0, x_683);
lean_ctor_set(x_771, 1, x_770);
lean_ctor_set(x_771, 2, x_769);
x_772 = lean_array_push(x_753, x_771);
x_773 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_773, 0, x_683);
lean_ctor_set(x_773, 1, x_684);
lean_ctor_set(x_773, 2, x_772);
x_774 = lean_array_push(x_681, x_773);
x_775 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_776 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_776, 0, x_683);
lean_ctor_set(x_776, 1, x_775);
lean_ctor_set(x_776, 2, x_774);
x_777 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
x_778 = lean_array_push(x_777, x_743);
x_779 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
x_780 = lean_array_push(x_778, x_779);
x_781 = lean_array_push(x_780, x_779);
x_782 = lean_array_push(x_781, x_749);
x_783 = lean_array_push(x_782, x_751);
x_784 = lean_array_push(x_783, x_776);
x_785 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_786 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_786, 0, x_683);
lean_ctor_set(x_786, 1, x_785);
lean_ctor_set(x_786, 2, x_784);
x_787 = lean_array_push(x_765, x_739);
x_788 = lean_array_push(x_787, x_779);
x_789 = lean_array_push(x_788, x_741);
x_790 = lean_array_push(x_789, x_786);
x_791 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
x_792 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_792, 0, x_683);
lean_ctor_set(x_792, 1, x_791);
lean_ctor_set(x_792, 2, x_790);
x_793 = lean_array_push(x_686, x_727);
x_794 = lean_array_push(x_793, x_792);
x_795 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_796 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_796, 0, x_683);
lean_ctor_set(x_796, 1, x_795);
lean_ctor_set(x_796, 2, x_794);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_797 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_798 = lean_array_push(x_797, x_706);
x_799 = lean_array_push(x_798, x_708);
x_800 = lean_array_push(x_799, x_716);
x_801 = lean_array_push(x_800, x_718);
x_802 = lean_array_push(x_801, x_723);
x_803 = lean_array_push(x_802, x_725);
x_804 = lean_array_push(x_803, x_796);
x_805 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_806 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_806, 0, x_683);
lean_ctor_set(x_806, 1, x_805);
lean_ctor_set(x_806, 2, x_804);
x_807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_673);
return x_807;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_808 = lean_ctor_get(x_5, 0);
lean_inc(x_808);
lean_dec(x_5);
x_809 = lean_array_push(x_681, x_808);
x_810 = l_Array_append___rarg(x_752, x_809);
x_811 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_811, 0, x_683);
lean_ctor_set(x_811, 1, x_684);
lean_ctor_set(x_811, 2, x_810);
x_812 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_813 = lean_array_push(x_812, x_811);
x_814 = lean_array_push(x_813, x_706);
x_815 = lean_array_push(x_814, x_708);
x_816 = lean_array_push(x_815, x_716);
x_817 = lean_array_push(x_816, x_718);
x_818 = lean_array_push(x_817, x_723);
x_819 = lean_array_push(x_818, x_725);
x_820 = lean_array_push(x_819, x_796);
x_821 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_822 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_822, 0, x_683);
lean_ctor_set(x_822, 1, x_821);
lean_ctor_set(x_822, 2, x_820);
x_823 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_673);
return x_823;
}
}
}
}
else
{
lean_object* x_824; lean_object* x_825; uint8_t x_826; 
x_824 = lean_ctor_get(x_1, 0);
lean_inc(x_824);
lean_dec(x_1);
x_825 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
x_826 = lean_name_eq(x_6, x_825);
if (x_826 == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_827 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_827, 0, x_6);
x_828 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99;
x_829 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_829, 0, x_828);
lean_ctor_set(x_829, 1, x_827);
x_830 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101;
x_831 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_831, 0, x_829);
lean_ctor_set(x_831, 1, x_830);
x_832 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(x_824, x_831, x_7, x_8, x_9);
return x_832;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; uint8_t x_843; 
lean_dec(x_6);
lean_inc(x_2);
x_833 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(x_2, x_7, x_8, x_9);
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
lean_dec(x_833);
x_836 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_7, x_8, x_835);
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 1);
lean_inc(x_838);
lean_dec(x_836);
x_839 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_838);
lean_dec(x_7);
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
lean_dec(x_839);
x_842 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_841);
lean_dec(x_8);
x_843 = !lean_is_exclusive(x_842);
if (x_843 == 0)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_844 = lean_ctor_get(x_842, 0);
x_845 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_837);
x_846 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_846, 0, x_837);
lean_ctor_set(x_846, 1, x_845);
x_847 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
lean_inc(x_840);
lean_inc(x_844);
x_848 = l_Lean_addMacroScope(x_844, x_847, x_840);
x_849 = lean_box(0);
x_850 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74;
lean_inc(x_837);
x_851 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_851, 0, x_837);
lean_ctor_set(x_851, 1, x_850);
lean_ctor_set(x_851, 2, x_848);
lean_ctor_set(x_851, 3, x_849);
x_852 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_853 = lean_array_push(x_852, x_834);
x_854 = lean_box(2);
x_855 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_856 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_856, 0, x_854);
lean_ctor_set(x_856, 1, x_855);
lean_ctor_set(x_856, 2, x_853);
x_857 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_858 = lean_array_push(x_857, x_851);
x_859 = lean_array_push(x_858, x_856);
x_860 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_861 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_861, 0, x_854);
lean_ctor_set(x_861, 1, x_860);
lean_ctor_set(x_861, 2, x_859);
x_862 = lean_array_push(x_857, x_3);
x_863 = lean_array_push(x_862, x_861);
x_864 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_865 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_865, 0, x_854);
lean_ctor_set(x_865, 1, x_864);
lean_ctor_set(x_865, 2, x_863);
x_866 = lean_array_push(x_852, x_865);
x_867 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_867, 0, x_854);
lean_ctor_set(x_867, 1, x_855);
lean_ctor_set(x_867, 2, x_866);
x_868 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
lean_inc(x_837);
x_869 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_869, 0, x_837);
lean_ctor_set(x_869, 1, x_868);
x_870 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_871 = lean_array_push(x_870, x_846);
x_872 = lean_array_push(x_871, x_867);
x_873 = lean_array_push(x_872, x_869);
x_874 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_875 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_875, 0, x_854);
lean_ctor_set(x_875, 1, x_874);
lean_ctor_set(x_875, 2, x_873);
x_876 = lean_array_push(x_852, x_875);
x_877 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_877, 0, x_854);
lean_ctor_set(x_877, 1, x_855);
lean_ctor_set(x_877, 2, x_876);
x_878 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_837);
x_879 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_879, 0, x_837);
lean_ctor_set(x_879, 1, x_878);
x_880 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_840);
lean_inc(x_844);
x_881 = l_Lean_addMacroScope(x_844, x_880, x_840);
x_882 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_837);
x_883 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_883, 0, x_837);
lean_ctor_set(x_883, 1, x_882);
lean_ctor_set(x_883, 2, x_881);
lean_ctor_set(x_883, 3, x_849);
x_884 = lean_mk_syntax_ident(x_2);
x_885 = lean_array_push(x_857, x_883);
x_886 = lean_array_push(x_885, x_884);
x_887 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_887, 0, x_854);
lean_ctor_set(x_887, 1, x_855);
lean_ctor_set(x_887, 2, x_886);
x_888 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_837);
x_889 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_889, 0, x_837);
lean_ctor_set(x_889, 1, x_888);
x_890 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
lean_inc(x_840);
lean_inc(x_844);
x_891 = l_Lean_addMacroScope(x_844, x_890, x_840);
x_892 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78;
x_893 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83;
lean_inc(x_837);
x_894 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_894, 0, x_837);
lean_ctor_set(x_894, 1, x_892);
lean_ctor_set(x_894, 2, x_891);
lean_ctor_set(x_894, 3, x_893);
x_895 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_837);
x_896 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_896, 0, x_837);
lean_ctor_set(x_896, 1, x_895);
x_897 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_837);
x_898 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_898, 0, x_837);
lean_ctor_set(x_898, 1, x_897);
x_899 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_inc(x_840);
lean_inc(x_844);
x_900 = l_Lean_addMacroScope(x_844, x_899, x_840);
x_901 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
lean_inc(x_837);
x_902 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_902, 0, x_837);
lean_ctor_set(x_902, 1, x_901);
lean_ctor_set(x_902, 2, x_900);
lean_ctor_set(x_902, 3, x_849);
x_903 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105;
lean_inc(x_840);
lean_inc(x_844);
x_904 = l_Lean_addMacroScope(x_844, x_903, x_840);
x_905 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104;
lean_inc(x_837);
x_906 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_906, 0, x_837);
lean_ctor_set(x_906, 1, x_905);
lean_ctor_set(x_906, 2, x_904);
lean_ctor_set(x_906, 3, x_849);
lean_inc(x_902);
x_907 = lean_array_push(x_857, x_902);
lean_inc(x_906);
x_908 = lean_array_push(x_907, x_906);
x_909 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_909, 0, x_854);
lean_ctor_set(x_909, 1, x_855);
lean_ctor_set(x_909, 2, x_908);
x_910 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
lean_inc(x_837);
x_911 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_911, 0, x_837);
lean_ctor_set(x_911, 1, x_910);
x_912 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112;
lean_inc(x_840);
lean_inc(x_844);
x_913 = l_Lean_addMacroScope(x_844, x_912, x_840);
x_914 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110;
x_915 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114;
lean_inc(x_837);
x_916 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_916, 0, x_837);
lean_ctor_set(x_916, 1, x_914);
lean_ctor_set(x_916, 2, x_913);
lean_ctor_set(x_916, 3, x_915);
x_917 = lean_array_push(x_852, x_824);
x_918 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_918, 0, x_854);
lean_ctor_set(x_918, 1, x_855);
lean_ctor_set(x_918, 2, x_917);
x_919 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
lean_inc(x_837);
x_920 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_920, 0, x_837);
lean_ctor_set(x_920, 1, x_919);
x_921 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
x_922 = lean_array_push(x_921, x_902);
x_923 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94;
x_924 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_924, 0, x_854);
lean_ctor_set(x_924, 1, x_923);
lean_ctor_set(x_924, 2, x_922);
x_925 = lean_array_push(x_852, x_924);
x_926 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_926, 0, x_854);
lean_ctor_set(x_926, 1, x_855);
lean_ctor_set(x_926, 2, x_925);
x_927 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
lean_inc(x_837);
x_928 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_928, 0, x_837);
lean_ctor_set(x_928, 1, x_927);
x_929 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_930 = l_Array_append___rarg(x_929, x_4);
x_931 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_837);
x_932 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_932, 0, x_837);
lean_ctor_set(x_932, 1, x_931);
x_933 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_837);
x_934 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_934, 0, x_837);
lean_ctor_set(x_934, 1, x_933);
x_935 = lean_array_push(x_852, x_934);
x_936 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
x_937 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_937, 0, x_854);
lean_ctor_set(x_937, 1, x_936);
lean_ctor_set(x_937, 2, x_935);
x_938 = lean_array_push(x_852, x_937);
x_939 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_939, 0, x_854);
lean_ctor_set(x_939, 1, x_855);
lean_ctor_set(x_939, 2, x_938);
x_940 = lean_array_push(x_852, x_939);
x_941 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_941, 0, x_854);
lean_ctor_set(x_941, 1, x_855);
lean_ctor_set(x_941, 2, x_940);
x_942 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_943 = l_Lean_addMacroScope(x_844, x_942, x_840);
x_944 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_945 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
x_946 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_946, 0, x_837);
lean_ctor_set(x_946, 1, x_944);
lean_ctor_set(x_946, 2, x_943);
lean_ctor_set(x_946, 3, x_945);
x_947 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_948 = lean_array_push(x_947, x_932);
x_949 = lean_array_push(x_948, x_941);
lean_inc(x_911);
x_950 = lean_array_push(x_949, x_911);
x_951 = lean_array_push(x_950, x_946);
x_952 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
x_953 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_953, 0, x_854);
lean_ctor_set(x_953, 1, x_952);
lean_ctor_set(x_953, 2, x_951);
x_954 = lean_array_push(x_930, x_953);
x_955 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_955, 0, x_854);
lean_ctor_set(x_955, 1, x_855);
lean_ctor_set(x_955, 2, x_954);
x_956 = lean_array_push(x_852, x_955);
x_957 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_958 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_958, 0, x_854);
lean_ctor_set(x_958, 1, x_957);
lean_ctor_set(x_958, 2, x_956);
x_959 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
x_960 = lean_array_push(x_959, x_920);
x_961 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
x_962 = lean_array_push(x_960, x_961);
x_963 = lean_array_push(x_962, x_961);
x_964 = lean_array_push(x_963, x_926);
x_965 = lean_array_push(x_964, x_928);
x_966 = lean_array_push(x_965, x_958);
x_967 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_968 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_968, 0, x_854);
lean_ctor_set(x_968, 1, x_967);
lean_ctor_set(x_968, 2, x_966);
x_969 = lean_array_push(x_947, x_918);
x_970 = lean_array_push(x_969, x_961);
lean_inc(x_911);
x_971 = lean_array_push(x_970, x_911);
x_972 = lean_array_push(x_971, x_968);
x_973 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
x_974 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_974, 0, x_854);
lean_ctor_set(x_974, 1, x_973);
lean_ctor_set(x_974, 2, x_972);
x_975 = lean_array_push(x_857, x_898);
lean_inc(x_975);
x_976 = lean_array_push(x_975, x_974);
x_977 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_978 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_978, 0, x_854);
lean_ctor_set(x_978, 1, x_977);
lean_ctor_set(x_978, 2, x_976);
x_979 = lean_array_push(x_857, x_906);
x_980 = lean_array_push(x_979, x_978);
x_981 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_981, 0, x_854);
lean_ctor_set(x_981, 1, x_855);
lean_ctor_set(x_981, 2, x_980);
x_982 = lean_array_push(x_857, x_916);
x_983 = lean_array_push(x_982, x_981);
x_984 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107;
x_985 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_985, 0, x_854);
lean_ctor_set(x_985, 1, x_984);
lean_ctor_set(x_985, 2, x_983);
x_986 = lean_array_push(x_947, x_909);
x_987 = lean_array_push(x_986, x_961);
x_988 = lean_array_push(x_987, x_911);
x_989 = lean_array_push(x_988, x_985);
x_990 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_990, 0, x_854);
lean_ctor_set(x_990, 1, x_973);
lean_ctor_set(x_990, 2, x_989);
x_991 = lean_array_push(x_975, x_990);
x_992 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_992, 0, x_854);
lean_ctor_set(x_992, 1, x_977);
lean_ctor_set(x_992, 2, x_991);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_993 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_994 = lean_array_push(x_993, x_877);
x_995 = lean_array_push(x_994, x_879);
x_996 = lean_array_push(x_995, x_887);
x_997 = lean_array_push(x_996, x_889);
x_998 = lean_array_push(x_997, x_894);
x_999 = lean_array_push(x_998, x_896);
x_1000 = lean_array_push(x_999, x_992);
x_1001 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_1002 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1002, 0, x_854);
lean_ctor_set(x_1002, 1, x_1001);
lean_ctor_set(x_1002, 2, x_1000);
lean_ctor_set(x_842, 0, x_1002);
return x_842;
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1003 = lean_ctor_get(x_5, 0);
lean_inc(x_1003);
lean_dec(x_5);
x_1004 = lean_array_push(x_852, x_1003);
x_1005 = l_Array_append___rarg(x_929, x_1004);
x_1006 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1006, 0, x_854);
lean_ctor_set(x_1006, 1, x_855);
lean_ctor_set(x_1006, 2, x_1005);
x_1007 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_1008 = lean_array_push(x_1007, x_1006);
x_1009 = lean_array_push(x_1008, x_877);
x_1010 = lean_array_push(x_1009, x_879);
x_1011 = lean_array_push(x_1010, x_887);
x_1012 = lean_array_push(x_1011, x_889);
x_1013 = lean_array_push(x_1012, x_894);
x_1014 = lean_array_push(x_1013, x_896);
x_1015 = lean_array_push(x_1014, x_992);
x_1016 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_1017 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1017, 0, x_854);
lean_ctor_set(x_1017, 1, x_1016);
lean_ctor_set(x_1017, 2, x_1015);
lean_ctor_set(x_842, 0, x_1017);
return x_842;
}
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1018 = lean_ctor_get(x_842, 0);
x_1019 = lean_ctor_get(x_842, 1);
lean_inc(x_1019);
lean_inc(x_1018);
lean_dec(x_842);
x_1020 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_837);
x_1021 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1021, 0, x_837);
lean_ctor_set(x_1021, 1, x_1020);
x_1022 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
lean_inc(x_840);
lean_inc(x_1018);
x_1023 = l_Lean_addMacroScope(x_1018, x_1022, x_840);
x_1024 = lean_box(0);
x_1025 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74;
lean_inc(x_837);
x_1026 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1026, 0, x_837);
lean_ctor_set(x_1026, 1, x_1025);
lean_ctor_set(x_1026, 2, x_1023);
lean_ctor_set(x_1026, 3, x_1024);
x_1027 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_1028 = lean_array_push(x_1027, x_834);
x_1029 = lean_box(2);
x_1030 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_1031 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1031, 0, x_1029);
lean_ctor_set(x_1031, 1, x_1030);
lean_ctor_set(x_1031, 2, x_1028);
x_1032 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_1033 = lean_array_push(x_1032, x_1026);
x_1034 = lean_array_push(x_1033, x_1031);
x_1035 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_1036 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1036, 0, x_1029);
lean_ctor_set(x_1036, 1, x_1035);
lean_ctor_set(x_1036, 2, x_1034);
x_1037 = lean_array_push(x_1032, x_3);
x_1038 = lean_array_push(x_1037, x_1036);
x_1039 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_1040 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1040, 0, x_1029);
lean_ctor_set(x_1040, 1, x_1039);
lean_ctor_set(x_1040, 2, x_1038);
x_1041 = lean_array_push(x_1027, x_1040);
x_1042 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1042, 0, x_1029);
lean_ctor_set(x_1042, 1, x_1030);
lean_ctor_set(x_1042, 2, x_1041);
x_1043 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
lean_inc(x_837);
x_1044 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1044, 0, x_837);
lean_ctor_set(x_1044, 1, x_1043);
x_1045 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_1046 = lean_array_push(x_1045, x_1021);
x_1047 = lean_array_push(x_1046, x_1042);
x_1048 = lean_array_push(x_1047, x_1044);
x_1049 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_1050 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1050, 0, x_1029);
lean_ctor_set(x_1050, 1, x_1049);
lean_ctor_set(x_1050, 2, x_1048);
x_1051 = lean_array_push(x_1027, x_1050);
x_1052 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1052, 0, x_1029);
lean_ctor_set(x_1052, 1, x_1030);
lean_ctor_set(x_1052, 2, x_1051);
x_1053 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_837);
x_1054 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1054, 0, x_837);
lean_ctor_set(x_1054, 1, x_1053);
x_1055 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_840);
lean_inc(x_1018);
x_1056 = l_Lean_addMacroScope(x_1018, x_1055, x_840);
x_1057 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_837);
x_1058 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1058, 0, x_837);
lean_ctor_set(x_1058, 1, x_1057);
lean_ctor_set(x_1058, 2, x_1056);
lean_ctor_set(x_1058, 3, x_1024);
x_1059 = lean_mk_syntax_ident(x_2);
x_1060 = lean_array_push(x_1032, x_1058);
x_1061 = lean_array_push(x_1060, x_1059);
x_1062 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1062, 0, x_1029);
lean_ctor_set(x_1062, 1, x_1030);
lean_ctor_set(x_1062, 2, x_1061);
x_1063 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_837);
x_1064 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1064, 0, x_837);
lean_ctor_set(x_1064, 1, x_1063);
x_1065 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
lean_inc(x_840);
lean_inc(x_1018);
x_1066 = l_Lean_addMacroScope(x_1018, x_1065, x_840);
x_1067 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78;
x_1068 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83;
lean_inc(x_837);
x_1069 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1069, 0, x_837);
lean_ctor_set(x_1069, 1, x_1067);
lean_ctor_set(x_1069, 2, x_1066);
lean_ctor_set(x_1069, 3, x_1068);
x_1070 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_837);
x_1071 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1071, 0, x_837);
lean_ctor_set(x_1071, 1, x_1070);
x_1072 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_837);
x_1073 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1073, 0, x_837);
lean_ctor_set(x_1073, 1, x_1072);
x_1074 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_inc(x_840);
lean_inc(x_1018);
x_1075 = l_Lean_addMacroScope(x_1018, x_1074, x_840);
x_1076 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
lean_inc(x_837);
x_1077 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1077, 0, x_837);
lean_ctor_set(x_1077, 1, x_1076);
lean_ctor_set(x_1077, 2, x_1075);
lean_ctor_set(x_1077, 3, x_1024);
x_1078 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105;
lean_inc(x_840);
lean_inc(x_1018);
x_1079 = l_Lean_addMacroScope(x_1018, x_1078, x_840);
x_1080 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104;
lean_inc(x_837);
x_1081 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1081, 0, x_837);
lean_ctor_set(x_1081, 1, x_1080);
lean_ctor_set(x_1081, 2, x_1079);
lean_ctor_set(x_1081, 3, x_1024);
lean_inc(x_1077);
x_1082 = lean_array_push(x_1032, x_1077);
lean_inc(x_1081);
x_1083 = lean_array_push(x_1082, x_1081);
x_1084 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1084, 0, x_1029);
lean_ctor_set(x_1084, 1, x_1030);
lean_ctor_set(x_1084, 2, x_1083);
x_1085 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
lean_inc(x_837);
x_1086 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1086, 0, x_837);
lean_ctor_set(x_1086, 1, x_1085);
x_1087 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112;
lean_inc(x_840);
lean_inc(x_1018);
x_1088 = l_Lean_addMacroScope(x_1018, x_1087, x_840);
x_1089 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110;
x_1090 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114;
lean_inc(x_837);
x_1091 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1091, 0, x_837);
lean_ctor_set(x_1091, 1, x_1089);
lean_ctor_set(x_1091, 2, x_1088);
lean_ctor_set(x_1091, 3, x_1090);
x_1092 = lean_array_push(x_1027, x_824);
x_1093 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1093, 0, x_1029);
lean_ctor_set(x_1093, 1, x_1030);
lean_ctor_set(x_1093, 2, x_1092);
x_1094 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
lean_inc(x_837);
x_1095 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1095, 0, x_837);
lean_ctor_set(x_1095, 1, x_1094);
x_1096 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
x_1097 = lean_array_push(x_1096, x_1077);
x_1098 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94;
x_1099 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1099, 0, x_1029);
lean_ctor_set(x_1099, 1, x_1098);
lean_ctor_set(x_1099, 2, x_1097);
x_1100 = lean_array_push(x_1027, x_1099);
x_1101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1101, 0, x_1029);
lean_ctor_set(x_1101, 1, x_1030);
lean_ctor_set(x_1101, 2, x_1100);
x_1102 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
lean_inc(x_837);
x_1103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1103, 0, x_837);
lean_ctor_set(x_1103, 1, x_1102);
x_1104 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_1105 = l_Array_append___rarg(x_1104, x_4);
x_1106 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_837);
x_1107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1107, 0, x_837);
lean_ctor_set(x_1107, 1, x_1106);
x_1108 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_837);
x_1109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1109, 0, x_837);
lean_ctor_set(x_1109, 1, x_1108);
x_1110 = lean_array_push(x_1027, x_1109);
x_1111 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
x_1112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1112, 0, x_1029);
lean_ctor_set(x_1112, 1, x_1111);
lean_ctor_set(x_1112, 2, x_1110);
x_1113 = lean_array_push(x_1027, x_1112);
x_1114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1114, 0, x_1029);
lean_ctor_set(x_1114, 1, x_1030);
lean_ctor_set(x_1114, 2, x_1113);
x_1115 = lean_array_push(x_1027, x_1114);
x_1116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1116, 0, x_1029);
lean_ctor_set(x_1116, 1, x_1030);
lean_ctor_set(x_1116, 2, x_1115);
x_1117 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_1118 = l_Lean_addMacroScope(x_1018, x_1117, x_840);
x_1119 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_1120 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
x_1121 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1121, 0, x_837);
lean_ctor_set(x_1121, 1, x_1119);
lean_ctor_set(x_1121, 2, x_1118);
lean_ctor_set(x_1121, 3, x_1120);
x_1122 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_1123 = lean_array_push(x_1122, x_1107);
x_1124 = lean_array_push(x_1123, x_1116);
lean_inc(x_1086);
x_1125 = lean_array_push(x_1124, x_1086);
x_1126 = lean_array_push(x_1125, x_1121);
x_1127 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8;
x_1128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1128, 0, x_1029);
lean_ctor_set(x_1128, 1, x_1127);
lean_ctor_set(x_1128, 2, x_1126);
x_1129 = lean_array_push(x_1105, x_1128);
x_1130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1130, 0, x_1029);
lean_ctor_set(x_1130, 1, x_1030);
lean_ctor_set(x_1130, 2, x_1129);
x_1131 = lean_array_push(x_1027, x_1130);
x_1132 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_1133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1133, 0, x_1029);
lean_ctor_set(x_1133, 1, x_1132);
lean_ctor_set(x_1133, 2, x_1131);
x_1134 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
x_1135 = lean_array_push(x_1134, x_1095);
x_1136 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
x_1137 = lean_array_push(x_1135, x_1136);
x_1138 = lean_array_push(x_1137, x_1136);
x_1139 = lean_array_push(x_1138, x_1101);
x_1140 = lean_array_push(x_1139, x_1103);
x_1141 = lean_array_push(x_1140, x_1133);
x_1142 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_1143 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1143, 0, x_1029);
lean_ctor_set(x_1143, 1, x_1142);
lean_ctor_set(x_1143, 2, x_1141);
x_1144 = lean_array_push(x_1122, x_1093);
x_1145 = lean_array_push(x_1144, x_1136);
lean_inc(x_1086);
x_1146 = lean_array_push(x_1145, x_1086);
x_1147 = lean_array_push(x_1146, x_1143);
x_1148 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
x_1149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1149, 0, x_1029);
lean_ctor_set(x_1149, 1, x_1148);
lean_ctor_set(x_1149, 2, x_1147);
x_1150 = lean_array_push(x_1032, x_1073);
lean_inc(x_1150);
x_1151 = lean_array_push(x_1150, x_1149);
x_1152 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_1153 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1153, 0, x_1029);
lean_ctor_set(x_1153, 1, x_1152);
lean_ctor_set(x_1153, 2, x_1151);
x_1154 = lean_array_push(x_1032, x_1081);
x_1155 = lean_array_push(x_1154, x_1153);
x_1156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1156, 0, x_1029);
lean_ctor_set(x_1156, 1, x_1030);
lean_ctor_set(x_1156, 2, x_1155);
x_1157 = lean_array_push(x_1032, x_1091);
x_1158 = lean_array_push(x_1157, x_1156);
x_1159 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107;
x_1160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1160, 0, x_1029);
lean_ctor_set(x_1160, 1, x_1159);
lean_ctor_set(x_1160, 2, x_1158);
x_1161 = lean_array_push(x_1122, x_1084);
x_1162 = lean_array_push(x_1161, x_1136);
x_1163 = lean_array_push(x_1162, x_1086);
x_1164 = lean_array_push(x_1163, x_1160);
x_1165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1165, 0, x_1029);
lean_ctor_set(x_1165, 1, x_1148);
lean_ctor_set(x_1165, 2, x_1164);
x_1166 = lean_array_push(x_1150, x_1165);
x_1167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1167, 0, x_1029);
lean_ctor_set(x_1167, 1, x_1152);
lean_ctor_set(x_1167, 2, x_1166);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1168 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_1169 = lean_array_push(x_1168, x_1052);
x_1170 = lean_array_push(x_1169, x_1054);
x_1171 = lean_array_push(x_1170, x_1062);
x_1172 = lean_array_push(x_1171, x_1064);
x_1173 = lean_array_push(x_1172, x_1069);
x_1174 = lean_array_push(x_1173, x_1071);
x_1175 = lean_array_push(x_1174, x_1167);
x_1176 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_1177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1177, 0, x_1029);
lean_ctor_set(x_1177, 1, x_1176);
lean_ctor_set(x_1177, 2, x_1175);
x_1178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1178, 0, x_1177);
lean_ctor_set(x_1178, 1, x_1019);
return x_1178;
}
else
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1179 = lean_ctor_get(x_5, 0);
lean_inc(x_1179);
lean_dec(x_5);
x_1180 = lean_array_push(x_1027, x_1179);
x_1181 = l_Array_append___rarg(x_1104, x_1180);
x_1182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1182, 0, x_1029);
lean_ctor_set(x_1182, 1, x_1030);
lean_ctor_set(x_1182, 2, x_1181);
x_1183 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_1184 = lean_array_push(x_1183, x_1182);
x_1185 = lean_array_push(x_1184, x_1052);
x_1186 = lean_array_push(x_1185, x_1054);
x_1187 = lean_array_push(x_1186, x_1062);
x_1188 = lean_array_push(x_1187, x_1064);
x_1189 = lean_array_push(x_1188, x_1069);
x_1190 = lean_array_push(x_1189, x_1071);
x_1191 = lean_array_push(x_1190, x_1167);
x_1192 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_1193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1193, 0, x_1029);
lean_ctor_set(x_1193, 1, x_1192);
lean_ctor_set(x_1193, 2, x_1191);
x_1194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1194, 0, x_1193);
lean_ctor_set(x_1194, 1, x_1019);
return x_1194;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid elab_rules command, specify category using `elab_rules : <cat> ...`", 75);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5(x_3, x_11, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Command_elabElabRulesAux___closed__2;
x_16 = l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(x_15, x_7, x_8, x_14);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
x_24 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1(x_5, x_3, x_2, x_21, x_1, x_23, x_7, x_8, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec(x_4);
x_28 = l_Lean_Syntax_getId(x_27);
lean_dec(x_27);
x_29 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1(x_5, x_3, x_2, x_25, x_1, x_28, x_7, x_8, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabElabRulesAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__4(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(6u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_15 = lean_name_mk_string(x_2, x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
lean_dec(x_13);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_21 = l_Lean_Syntax_getId(x_3);
lean_inc(x_10);
lean_inc(x_9);
x_22 = l_Lean_Elab_Command_resolveSyntaxKind(x_21, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Command_elabElabRulesAux(x_4, x_5, x_23, x_6, x_8, x_20, x_9, x_10, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(5u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(2u);
lean_inc(x_12);
x_15 = l_Lean_Syntax_matchesNull(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_12, x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Command_elabElabRules___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7, x_20, x_19, x_8, x_9, x_10);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Command_elabElabRules___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7, x_23, x_22, x_8, x_9, x_10);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elab_rules", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<=", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("kind", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Command_getCurrMacroScope(x_9, x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Command_getMainModule___rarg(x_10, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_19 = x_17;
} else {
 lean_dec_ref(x_17);
 x_19 = lean_box(0);
}
x_20 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
lean_inc(x_13);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_23 = l_Array_append___rarg(x_22, x_8);
x_24 = lean_box(2);
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_28);
if (lean_obj_tag(x_6) == 0)
{
x_30 = x_22;
goto block_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_6, 0);
lean_inc(x_87);
lean_dec(x_6);
x_88 = lean_array_push(x_27, x_87);
x_30 = x_88;
goto block_86;
}
block_86:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = l_Array_append___rarg(x_22, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
lean_ctor_set(x_32, 2, x_31);
x_33 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2;
x_34 = lean_array_push(x_33, x_32);
x_35 = lean_array_push(x_34, x_2);
x_36 = lean_array_push(x_35, x_21);
if (lean_obj_tag(x_7) == 0)
{
x_37 = x_22;
goto block_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_70 = lean_ctor_get(x_7, 0);
lean_inc(x_70);
lean_dec(x_7);
x_71 = lean_mk_syntax_ident(x_70);
x_72 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4;
lean_inc(x_13);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_13);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5;
lean_inc(x_13);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_13);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_13);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_13);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6;
lean_inc(x_13);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_13);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7;
x_81 = lean_array_push(x_80, x_73);
x_82 = lean_array_push(x_81, x_75);
x_83 = lean_array_push(x_82, x_77);
x_84 = lean_array_push(x_83, x_71);
x_85 = lean_array_push(x_84, x_79);
x_37 = x_85;
goto block_69;
}
block_69:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l_Array_append___rarg(x_22, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_push(x_36, x_39);
if (lean_obj_tag(x_5) == 0)
{
x_41 = x_22;
goto block_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_5, 0);
lean_inc(x_63);
lean_dec(x_5);
x_64 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_13);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_13);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_67 = lean_array_push(x_66, x_65);
x_68 = lean_array_push(x_67, x_63);
x_41 = x_68;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Array_append___rarg(x_22, x_41);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_array_push(x_40, x_43);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_13);
x_45 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_46 = lean_array_push(x_44, x_45);
x_47 = lean_array_push(x_46, x_29);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_24);
lean_ctor_set(x_48, 1, x_4);
lean_ctor_set(x_48, 2, x_47);
if (lean_is_scalar(x_19)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_19;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_18);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
lean_dec(x_3);
x_51 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3;
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_13);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_54 = lean_array_push(x_53, x_52);
x_55 = lean_array_push(x_54, x_50);
x_56 = l_Array_append___rarg(x_22, x_55);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_24);
lean_ctor_set(x_57, 1, x_25);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_array_push(x_44, x_57);
x_59 = lean_array_push(x_58, x_29);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_24);
lean_ctor_set(x_60, 1, x_4);
lean_ctor_set(x_60, 2, x_59);
if (lean_is_scalar(x_19)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_19;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_18);
return x_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(6u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_15 = lean_name_mk_string(x_2, x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
lean_dec(x_13);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lambda__3___boxed), 11, 6);
lean_closure_set(x_21, 0, x_15);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_8);
lean_closure_set(x_21, 3, x_4);
lean_closure_set(x_21, 4, x_5);
lean_closure_set(x_21, 5, x_6);
x_22 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
x_23 = l_Lean_Elab_Command_expandNoKindMacroRulesAux(x_20, x_22, x_21, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(5u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(2u);
lean_inc(x_12);
x_15 = l_Lean_Syntax_matchesNull(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_12, x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Command_elabElabRules___lambda__4(x_1, x_2, x_3, x_4, x_7, x_5, x_20, x_19, x_8, x_9, x_10);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Command_elabElabRules___lambda__4(x_1, x_2, x_3, x_4, x_7, x_5, x_23, x_22, x_8, x_9, x_10);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("attrKind", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__5;
x_12 = lean_name_mk_string(x_2, x_11);
x_13 = l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1;
lean_inc(x_12);
x_14 = lean_name_mk_string(x_12, x_13);
lean_inc(x_10);
x_15 = l_Lean_Syntax_isOfKind(x_10, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
x_20 = l_Lean_Syntax_matchesNull(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_3);
x_21 = lean_unsigned_to_nat(5u);
lean_inc(x_18);
x_22 = l_Lean_Syntax_matchesNull(x_18, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_8);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Lean_Syntax_getArg(x_18, x_17);
lean_dec(x_18);
x_25 = lean_unsigned_to_nat(4u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
x_27 = l_Lean_Syntax_isNone(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(2u);
lean_inc(x_26);
x_29 = l_Lean_Syntax_matchesNull(x_26, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_8);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Syntax_getArg(x_26, x_9);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Command_elabElabRules___lambda__2(x_1, x_12, x_24, x_5, x_10, x_33, x_32, x_6, x_7, x_8);
lean_dec(x_24);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
x_35 = lean_box(0);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Command_elabElabRules___lambda__2(x_1, x_12, x_24, x_5, x_10, x_36, x_35, x_6, x_7, x_8);
lean_dec(x_24);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_18);
x_38 = lean_unsigned_to_nat(4u);
x_39 = l_Lean_Syntax_getArg(x_1, x_38);
x_40 = l_Lean_Syntax_isNone(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_unsigned_to_nat(2u);
lean_inc(x_39);
x_42 = l_Lean_Syntax_matchesNull(x_39, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_43 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_8);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = l_Lean_Syntax_getArg(x_39, x_9);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Command_elabElabRules___lambda__5(x_1, x_12, x_10, x_3, x_5, x_46, x_45, x_6, x_7, x_8);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_39);
x_48 = lean_box(0);
x_49 = lean_box(0);
x_50 = l_Lean_Elab_Command_elabElabRules___lambda__5(x_1, x_12, x_10, x_3, x_5, x_49, x_48, x_6, x_7, x_8);
return x_50;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_2 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("docComment", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_2 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_4);
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_15 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4;
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Command_elabElabRules___lambda__6(x_1, x_19, x_5, x_20, x_18, x_2, x_3, x_4);
lean_dec(x_1);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
x_22 = lean_box(0);
x_23 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4;
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Command_elabElabRules___lambda__6(x_1, x_23, x_5, x_24, x_22, x_2, x_3, x_4);
lean_dec(x_1);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lambda__7), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Command_elabElabRules___closed__1;
x_6 = l_Lean_Elab_Command_adaptExpander(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabElabRules___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabElabRules___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabElabRules___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabElabRules___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabElabRules___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabElabRules___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabElabRules", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3;
x_3 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(78u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2;
x_4 = lean_unsigned_to_nat(32u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4;
x_2 = lean_unsigned_to_nat(39u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5;
x_4 = lean_unsigned_to_nat(52u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Elab_Command_expandMacroArg(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_11, x_2, x_13);
x_2 = x_16;
x_3 = x_17;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("syntax", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("namedName", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("name", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("namedPrio", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("priority", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("quot", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`(", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("precedence", 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_19 = l_Lean_Elab_Command_getScope___rarg(x_17, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_15);
x_23 = l_Lean_Name_append(x_22, x_15);
lean_dec(x_22);
x_24 = lean_box(2);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_1);
x_26 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__6(x_15, x_16, x_17, x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_16, x_17, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Command_getCurrMacroScope(x_16, x_17, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Elab_Command_getMainModule___rarg(x_17, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Elab_Command_elabElab___lambda__1___closed__1;
lean_inc(x_2);
x_37 = lean_name_mk_string(x_2, x_36);
lean_inc(x_30);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Elab_Command_elabElab___lambda__1___closed__2;
lean_inc(x_2);
x_40 = lean_name_mk_string(x_2, x_39);
x_41 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4;
lean_inc(x_30);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Elab_Command_elabElab___lambda__1___closed__3;
lean_inc(x_30);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_30);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_30);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6;
lean_inc(x_30);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_30);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7;
x_50 = lean_array_push(x_49, x_42);
lean_inc(x_50);
x_51 = lean_array_push(x_50, x_44);
lean_inc(x_46);
x_52 = lean_array_push(x_51, x_46);
x_53 = lean_array_push(x_52, x_27);
lean_inc(x_48);
x_54 = lean_array_push(x_53, x_48);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_24);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 2, x_54);
x_56 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5;
x_57 = lean_array_push(x_56, x_55);
x_58 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_24);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_57);
x_60 = l_Lean_Elab_Command_elabElab___lambda__1___closed__4;
lean_inc(x_2);
x_61 = lean_name_mk_string(x_2, x_60);
x_62 = l_Lean_Elab_Command_elabElab___lambda__1___closed__5;
lean_inc(x_30);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_30);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Nat_repr(x_3);
x_65 = l_Lean_Syntax_mkNumLit(x_64, x_24);
x_66 = lean_array_push(x_50, x_63);
x_67 = lean_array_push(x_66, x_46);
x_68 = lean_array_push(x_67, x_65);
lean_inc(x_48);
x_69 = lean_array_push(x_68, x_48);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_24);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_69);
x_71 = lean_array_push(x_56, x_70);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_24);
lean_ctor_set(x_72, 1, x_58);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_array_get_size(x_4);
x_74 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_75 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__2(x_74, x_5, x_4);
x_76 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4;
x_77 = l_Array_append___rarg(x_76, x_75);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_24);
lean_ctor_set(x_78, 1, x_58);
lean_ctor_set(x_78, 2, x_77);
x_79 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_30);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_30);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
x_82 = lean_name_mk_string(x_2, x_81);
x_83 = l_Lean_Elab_Command_elabElab___lambda__1___closed__7;
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_24);
lean_ctor_set(x_84, 1, x_6);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_30);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_30);
lean_ctor_set(x_85, 1, x_81);
x_86 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
lean_inc(x_80);
x_87 = lean_array_push(x_86, x_80);
lean_inc(x_7);
lean_inc(x_87);
x_88 = lean_array_push(x_87, x_7);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_24);
lean_ctor_set(x_89, 1, x_58);
lean_ctor_set(x_89, 2, x_88);
x_90 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
lean_inc(x_8);
x_91 = lean_name_mk_string(x_8, x_90);
x_92 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__7;
lean_inc(x_8);
x_93 = lean_name_mk_string(x_8, x_92);
x_94 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1;
lean_inc(x_30);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_30);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Elab_Command_elabElab___lambda__1___closed__8;
x_97 = lean_name_mk_string(x_8, x_96);
x_98 = l_Lean_Elab_Command_elabElab___lambda__1___closed__9;
lean_inc(x_30);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_30);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_101 = lean_array_push(x_100, x_99);
x_102 = lean_array_push(x_101, x_25);
x_103 = lean_array_push(x_102, x_48);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_24);
lean_ctor_set(x_104, 1, x_97);
lean_ctor_set(x_104, 2, x_103);
x_105 = lean_array_push(x_56, x_104);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_24);
lean_ctor_set(x_106, 1, x_58);
lean_ctor_set(x_106, 2, x_105);
x_107 = lean_array_push(x_56, x_106);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_24);
lean_ctor_set(x_108, 1, x_58);
lean_ctor_set(x_108, 2, x_107);
x_109 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6;
lean_inc(x_30);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_30);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7;
x_112 = lean_array_push(x_111, x_95);
x_113 = lean_array_push(x_112, x_108);
x_114 = lean_array_push(x_113, x_110);
x_115 = lean_array_push(x_114, x_9);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_24);
lean_ctor_set(x_116, 1, x_93);
lean_ctor_set(x_116, 2, x_115);
x_117 = lean_array_push(x_56, x_116);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_24);
lean_ctor_set(x_118, 1, x_58);
lean_ctor_set(x_118, 2, x_117);
x_119 = lean_array_push(x_56, x_118);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_24);
lean_ctor_set(x_120, 1, x_91);
lean_ctor_set(x_120, 2, x_119);
if (lean_obj_tag(x_14) == 0)
{
x_121 = x_76;
goto block_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_14, 0);
lean_inc(x_174);
lean_dec(x_14);
x_175 = lean_array_push(x_56, x_174);
x_121 = x_175;
goto block_173;
}
block_173:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_122 = l_Array_append___rarg(x_76, x_121);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_24);
lean_ctor_set(x_123, 1, x_58);
lean_ctor_set(x_123, 2, x_122);
x_124 = l_Lean_Elab_Command_elabElab___lambda__1___closed__6;
lean_inc(x_123);
x_125 = lean_array_push(x_124, x_123);
x_126 = lean_array_push(x_125, x_10);
x_127 = lean_array_push(x_126, x_38);
x_128 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2;
x_129 = lean_array_push(x_128, x_123);
x_130 = lean_array_push(x_129, x_84);
x_131 = lean_array_push(x_130, x_85);
x_132 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
x_133 = lean_array_push(x_131, x_132);
x_134 = lean_array_push(x_133, x_89);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_87);
lean_dec(x_13);
x_135 = x_76;
goto block_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_12, 0);
lean_inc(x_167);
lean_dec(x_12);
x_168 = l_Lean_Elab_Command_elabElab___lambda__1___closed__10;
x_169 = lean_name_mk_string(x_13, x_168);
x_170 = lean_array_push(x_87, x_167);
x_171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_171, 0, x_24);
lean_ctor_set(x_171, 1, x_169);
lean_ctor_set(x_171, 2, x_170);
x_172 = lean_array_push(x_56, x_171);
x_135 = x_172;
goto block_166;
}
block_166:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_136 = l_Array_append___rarg(x_76, x_135);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_24);
lean_ctor_set(x_137, 1, x_58);
lean_ctor_set(x_137, 2, x_136);
x_138 = lean_array_push(x_127, x_137);
x_139 = lean_array_push(x_138, x_59);
x_140 = lean_array_push(x_139, x_72);
x_141 = lean_array_push(x_140, x_78);
x_142 = lean_array_push(x_141, x_80);
x_143 = lean_array_push(x_142, x_7);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_24);
lean_ctor_set(x_144, 1, x_37);
lean_ctor_set(x_144, 2, x_143);
x_145 = lean_array_push(x_86, x_144);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_30);
x_146 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_147 = lean_array_push(x_134, x_146);
x_148 = lean_array_push(x_147, x_120);
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_24);
lean_ctor_set(x_149, 1, x_82);
lean_ctor_set(x_149, 2, x_148);
x_150 = lean_array_push(x_145, x_149);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_24);
lean_ctor_set(x_151, 1, x_58);
lean_ctor_set(x_151, 2, x_150);
x_152 = l_Lean_Elab_Command_elabCommand(x_151, x_16, x_17, x_35);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_153 = lean_ctor_get(x_11, 0);
lean_inc(x_153);
lean_dec(x_11);
x_154 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3;
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_30);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_array_push(x_86, x_155);
x_157 = lean_array_push(x_156, x_153);
x_158 = l_Array_append___rarg(x_76, x_157);
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_24);
lean_ctor_set(x_159, 1, x_58);
lean_ctor_set(x_159, 2, x_158);
x_160 = lean_array_push(x_134, x_159);
x_161 = lean_array_push(x_160, x_120);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_24);
lean_ctor_set(x_162, 1, x_82);
lean_ctor_set(x_162, 2, x_161);
x_163 = lean_array_push(x_145, x_162);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_24);
lean_ctor_set(x_164, 1, x_58);
lean_ctor_set(x_164, 2, x_163);
x_165 = l_Lean_Elab_Command_elabCommand(x_164, x_16, x_17, x_35);
return x_165;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_evalOptPrio), 3, 1);
lean_closure_set(x_21, 0, x_3);
lean_inc(x_16);
lean_inc(x_15);
x_22 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__4(x_21, x_15, x_16, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_20);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
lean_inc(x_16);
lean_inc(x_15);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__1(x_26, x_27, x_20, x_15, x_16, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Array_unzip___rarg(x_29);
lean_dec(x_29);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Syntax_getId(x_6);
x_35 = lean_box(2);
x_36 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3;
lean_inc(x_32);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_32);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkNameFromParserSyntax), 4, 2);
lean_closure_set(x_38, 0, x_34);
lean_closure_set(x_38, 1, x_37);
lean_inc(x_16);
lean_inc(x_15);
x_39 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Command_elabSyntax___spec__9(x_38, x_15, x_16, x_30);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Command_elabElab___lambda__1(x_33, x_4, x_23, x_32, x_27, x_5, x_6, x_7, x_19, x_8, x_14, x_9, x_10, x_11, x_40, x_15, x_16, x_41);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_31, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_ctor_get(x_12, 0);
lean_inc(x_49);
lean_dec(x_12);
x_50 = l_Lean_Syntax_getId(x_49);
lean_dec(x_49);
x_51 = l_Lean_Elab_Command_elabElab___lambda__1(x_48, x_4, x_23, x_47, x_27, x_5, x_6, x_7, x_19, x_8, x_14, x_9, x_10, x_11, x_50, x_15, x_16, x_30);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_28);
if (x_52 == 0)
{
return x_28;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_28, 0);
x_54 = lean_ctor_get(x_28, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_28);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabTail", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(6u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(7u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = l_Lean_Elab_Command_elabElab___lambda__3___closed__1;
lean_inc(x_2);
x_20 = lean_name_mk_string(x_2, x_19);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isOfKind(x_18, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_18, x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_Syntax_getArg(x_18, x_25);
x_27 = l_Lean_Syntax_isNone(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_inc(x_26);
x_28 = l_Lean_Syntax_matchesNull(x_26, x_25);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_14);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lean_Syntax_getArg(x_26, x_23);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Command_elabElab___lambda__2(x_18, x_16, x_11, x_2, x_3, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_32, x_31, x_12, x_13, x_14);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Command_elabElab___lambda__2(x_18, x_16, x_11, x_2, x_3, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_35, x_34, x_12, x_13, x_14);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_9);
x_14 = lean_unsigned_to_nat(5u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
x_18 = l_Lean_Syntax_matchesNull(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_15, x_20);
lean_dec(x_15);
x_22 = l_Lean_Elab_Command_elabElab___lambda__1___closed__4;
lean_inc(x_2);
x_23 = lean_name_mk_string(x_2, x_22);
lean_inc(x_21);
x_24 = l_Lean_Syntax_isOfKind(x_21, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_13);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_unsigned_to_nat(3u);
x_27 = l_Lean_Syntax_getArg(x_21, x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Command_elabElab___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_29, x_28, x_11, x_12, x_13);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_15);
x_31 = lean_box(0);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Command_elabElab___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_32, x_31, x_11, x_12, x_13);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(4u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_14);
x_17 = l_Lean_Syntax_matchesNull(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_14, x_19);
lean_dec(x_14);
x_21 = l_Lean_Elab_Command_elabElab___lambda__1___closed__2;
lean_inc(x_2);
x_22 = lean_name_mk_string(x_2, x_21);
lean_inc(x_20);
x_23 = l_Lean_Syntax_isOfKind(x_20, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_12);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_unsigned_to_nat(3u);
x_26 = l_Lean_Syntax_getArg(x_20, x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Command_elabElab___lambda__4(x_1, x_2, x_3, x_4, x_5, x_9, x_6, x_7, x_28, x_27, x_10, x_11, x_12);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Command_elabElab___lambda__4(x_1, x_2, x_3, x_4, x_5, x_9, x_6, x_7, x_31, x_30, x_10, x_11, x_12);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__5;
lean_inc(x_2);
x_12 = lean_name_mk_string(x_2, x_11);
x_13 = l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1;
lean_inc(x_12);
x_14 = lean_name_mk_string(x_12, x_13);
lean_inc(x_10);
x_15 = l_Lean_Syntax_isOfKind(x_10, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc(x_18);
x_20 = l_Lean_Syntax_matchesNull(x_18, x_9);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_18, x_22);
lean_dec(x_18);
x_24 = l_Lean_Elab_Command_elabElab___lambda__1___closed__10;
lean_inc(x_2);
x_25 = lean_name_mk_string(x_2, x_24);
lean_inc(x_23);
x_26 = l_Lean_Syntax_isOfKind(x_23, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_Syntax_getArg(x_23, x_9);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Command_elabElab___lambda__5(x_1, x_3, x_14, x_12, x_10, x_2, x_5, x_30, x_29, x_6, x_7, x_8);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Command_elabElab___lambda__5(x_1, x_3, x_14, x_12, x_10, x_2, x_5, x_33, x_32, x_6, x_7, x_8);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_2 = l_Lean_Elab_Command_elabElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabElab___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_4);
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_15 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabAuxDef___spec__1___rarg(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4;
x_20 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Command_elabElab___lambda__6(x_1, x_19, x_20, x_21, x_18, x_2, x_3, x_4);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_23 = lean_box(0);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4;
x_25 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Command_elabElab___lambda__6(x_1, x_24, x_25, x_26, x_23, x_2, x_3, x_4);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__1(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElab___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
size_t x_19; lean_object* x_20; 
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l_Lean_Elab_Command_elabElab___lambda__1(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElab___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Command_elabElab___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabElab", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l___regBuiltin_Lean_Elab_Command_elabElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElab), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElab(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3;
x_3 = l_Lean_Elab_Command_elabElab___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabElab___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabElab___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(81u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(94u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(81u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(81u);
x_2 = lean_unsigned_to_nat(12u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__5;
x_4 = lean_unsigned_to_nat(12u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElab_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabElab___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MacroArgUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_withExpectedType___closed__1 = _init_l_Lean_Elab_Command_withExpectedType___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_withExpectedType___closed__1);
l_Lean_Elab_Command_withExpectedType___closed__2 = _init_l_Lean_Elab_Command_withExpectedType___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_withExpectedType___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabElabRulesAux___spec__1___rarg___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__6);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__7);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__8 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__8();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__8);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__9 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__9();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__9);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__10 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__10();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__10);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__11 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__11();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__11);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__12 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__12();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__12);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__13 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__13();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__13);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__14 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__14();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__14);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__15 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__15();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__15);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__16 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__16();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___lambda__2___closed__16);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__6);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__7 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__7);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__5___closed__8);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114);
l_Lean_Elab_Command_elabElabRulesAux___closed__1 = _init_l_Lean_Elab_Command_elabElabRulesAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___closed__1);
l_Lean_Elab_Command_elabElabRulesAux___closed__2 = _init_l_Lean_Elab_Command_elabElabRulesAux___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___closed__2);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7);
l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1 = _init_l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1);
l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1 = _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1);
l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2 = _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2);
l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3 = _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3);
l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4 = _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4);
l_Lean_Elab_Command_elabElabRules___closed__1 = _init_l_Lean_Elab_Command_elabElabRules___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___closed__1);
l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1);
l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2);
l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3);
l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4);
res = l___regBuiltin_Lean_Elab_Command_elabElabRules(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabElab___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__1);
l_Lean_Elab_Command_elabElab___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__2);
l_Lean_Elab_Command_elabElab___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__3);
l_Lean_Elab_Command_elabElab___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__4);
l_Lean_Elab_Command_elabElab___lambda__1___closed__5 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__5);
l_Lean_Elab_Command_elabElab___lambda__1___closed__6 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__6);
l_Lean_Elab_Command_elabElab___lambda__1___closed__7 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__7);
l_Lean_Elab_Command_elabElab___lambda__1___closed__8 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__8);
l_Lean_Elab_Command_elabElab___lambda__1___closed__9 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__9);
l_Lean_Elab_Command_elabElab___lambda__1___closed__10 = _init_l_Lean_Elab_Command_elabElab___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__1___closed__10);
l_Lean_Elab_Command_elabElab___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabElab___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___lambda__3___closed__1);
l_Lean_Elab_Command_elabElab___closed__1 = _init_l_Lean_Elab_Command_elabElab___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___closed__1);
l_Lean_Elab_Command_elabElab___closed__2 = _init_l_Lean_Elab_Command_elabElab___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElab___closed__2);
l___regBuiltin_Lean_Elab_Command_elabElab___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabElab___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab___closed__1);
l___regBuiltin_Lean_Elab_Command_elabElab___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabElab___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab___closed__2);
l___regBuiltin_Lean_Elab_Command_elabElab___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabElab___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabElab(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElab_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabElab_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
