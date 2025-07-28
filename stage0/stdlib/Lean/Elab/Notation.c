// Lean compiler output
// Module: Lean.Elab.Notation
// Imports: Lean.Elab.Syntax Lean.Elab.AuxDef Lean.Elab.BuiltinNotation Lean.Parser.Syntax
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
static lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__2;
lean_object* l_Lean_Elab_toAttributeKind(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__55;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__50;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__18;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
uint8_t l_Lean_Elab_Command_isLocalAttrKind(lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_setHeadInfo(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__7;
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__54;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__1;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__14;
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__35;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__18;
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__16;
static lean_object* l_Lean_Elab_Command_removeParentheses___closed__4;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__38;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__29;
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__65;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__23;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__9;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__66;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__7;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__48;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__21;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__15;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__3;
lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
static lean_object* l_Lean_Elab_Command_removeParentheses___closed__0;
static lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__61;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotation(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotation___closed__6;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
lean_object* l_Lean_Macro_getCurrNamespace(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__30;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__46;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__59;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__2;
static lean_object* l_Lean_Elab_Command_expandNotation___closed__2;
static lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__7;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__17;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__0;
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__5;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__62;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_removeParentheses___closed__5;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__37;
uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
static lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__5;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__6;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__52;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Command_expandNotation___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotation___closed__0;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__21;
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__4;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__53;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__8;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__45;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__14;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__15;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__49;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__1;
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__68;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__26;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__2;
static lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_removeParentheses___closed__2;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__67;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__51;
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_strLitToPattern___redArg(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__2;
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotation___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__41;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__22;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__9;
lean_object* l_Lean_TSyntax_getHygieneInfo(lean_object*);
lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__19;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__69;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__43;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__10;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__27;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__11;
static lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__6;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__8;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__58;
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__3;
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__1;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__39;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__64;
static lean_object* l_Lean_Elab_Command_addInheritDocDefault___closed__3;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Command_expandNotation___closed__5;
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__60;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__10;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__12;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__22;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__25;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__57;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__0;
static lean_object* l_Lean_Elab_Command_removeParentheses___closed__3;
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__16;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__4;
static lean_object* l_Lean_Elab_Command_removeParentheses___closed__1;
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__63;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__47;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Command_expandNotation___closed__3;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__5;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__34;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__3;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__28;
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__42;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__24;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__36;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__56;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__31;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3(size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__40;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__13;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__19;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__17;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__20;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__13;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__33;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__32;
static lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__0;
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7;
static lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3;
static lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__11;
static lean_object* l_Lean_Elab_Command_mkUnexpander___closed__44;
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(x_1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
x_8 = l_Lean_Syntax_getId(x_1);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
return x_9;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
lean_inc(x_2);
x_4 = l_Lean_Syntax_isOfKind(x_2, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(x_1, x_7, x_8, x_6);
lean_ctor_set(x_2, 2, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(x_1, x_13, x_14, x_12);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
else
{
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
return x_2;
}
else
{
if (x_19 == 0)
{
lean_dec(x_18);
return x_2;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_22 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(x_2, x_1, x_20, x_21);
if (x_22 == 0)
{
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3;
x_24 = lean_box(0);
x_25 = l_Lean_Syntax_mkAntiquotNode(x_23, x_2, x_17, x_24, x_4);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attrKind", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Attr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simple", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inherit_doc", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_12 = lean_array_uget(x_10, x_9);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_10, x_9, x_13);
lean_inc(x_12);
x_21 = l_Lean_Syntax_isOfKind(x_12, x_7);
if (x_21 == 0)
{
x_15 = x_12;
goto block_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = l_Lean_Syntax_getArg(x_12, x_13);
x_23 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_24 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_23);
lean_inc(x_22);
x_25 = l_Lean_Syntax_isOfKind(x_22, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
x_15 = x_12;
goto block_20;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Syntax_getArg(x_22, x_13);
lean_dec(x_22);
x_27 = l_Lean_Syntax_matchesNull(x_26, x_13);
if (x_27 == 0)
{
lean_dec(x_24);
x_15 = x_12;
goto block_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = l_Lean_Syntax_getArg(x_12, x_28);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__1;
x_31 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__2;
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_32 = l_Lean_Name_mkStr4(x_1, x_2, x_30, x_31);
lean_inc(x_29);
x_33 = l_Lean_Syntax_isOfKind(x_29, x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_24);
x_15 = x_12;
goto block_20;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Syntax_getArg(x_29, x_13);
lean_inc(x_34);
x_35 = l_Lean_Syntax_isOfKind(x_34, x_4);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_24);
x_15 = x_12;
goto block_20;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Syntax_getArg(x_29, x_28);
lean_dec(x_29);
x_37 = l_Lean_Syntax_matchesNull(x_36, x_13);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_24);
x_15 = x_12;
goto block_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = l_Lean_Syntax_getId(x_34);
x_39 = lean_erase_macro_scopes(x_38);
x_40 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__4;
x_41 = lean_name_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_24);
x_15 = x_12;
goto block_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_12);
x_42 = lean_box(0);
x_43 = l_Lean_SourceInfo_fromRef(x_42, x_5);
x_44 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_45 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7;
lean_inc(x_43);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
lean_inc(x_43);
x_47 = l_Lean_Syntax_node1(x_43, x_24, x_46);
lean_inc(x_6);
lean_inc(x_43);
x_48 = l_Lean_Syntax_node1(x_43, x_44, x_6);
lean_inc(x_43);
x_49 = l_Lean_Syntax_node2(x_43, x_32, x_34, x_48);
lean_inc(x_7);
x_50 = l_Lean_Syntax_node2(x_43, x_7, x_47, x_49);
x_15 = x_50;
goto block_20;
}
}
}
}
}
}
}
block_20:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_usize_add(x_9, x_16);
x_18 = lean_array_uset(x_14, x_9, x_15);
x_9 = x_17;
x_10 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg(x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = l_Lean_SourceInfo_fromRef(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7;
x_2 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_3 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__0;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_10, x_9);
if (x_12 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_22; 
x_13 = lean_array_uget(x_11, x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_11, x_10, x_14);
lean_inc(x_13);
x_22 = l_Lean_Syntax_isOfKind(x_13, x_8);
if (x_22 == 0)
{
x_16 = x_13;
goto block_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l_Lean_Syntax_getArg(x_13, x_1);
x_24 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0;
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_25 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_24);
lean_inc(x_23);
x_26 = l_Lean_Syntax_isOfKind(x_23, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_23);
x_16 = x_13;
goto block_21;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Syntax_getArg(x_23, x_1);
lean_dec(x_23);
x_28 = l_Lean_Syntax_matchesNull(x_27, x_1);
if (x_28 == 0)
{
lean_dec(x_25);
x_16 = x_13;
goto block_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = l_Lean_Syntax_getArg(x_13, x_5);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__1;
x_31 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__2;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_32 = l_Lean_Name_mkStr4(x_2, x_3, x_30, x_31);
lean_inc(x_29);
x_33 = l_Lean_Syntax_isOfKind(x_29, x_32);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_25);
x_16 = x_13;
goto block_21;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Syntax_getArg(x_29, x_1);
lean_inc(x_34);
x_35 = l_Lean_Syntax_isOfKind(x_34, x_6);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_25);
x_16 = x_13;
goto block_21;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Syntax_getArg(x_29, x_5);
lean_dec(x_29);
x_37 = l_Lean_Syntax_matchesNull(x_36, x_1);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_25);
x_16 = x_13;
goto block_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = l_Lean_Syntax_getId(x_34);
x_39 = lean_erase_macro_scopes(x_38);
x_40 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__4;
x_41 = lean_name_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_25);
x_16 = x_13;
goto block_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_13);
x_42 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__0;
x_43 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_44 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__1;
x_45 = l_Lean_Syntax_node1(x_42, x_25, x_44);
lean_inc(x_7);
x_46 = l_Lean_Syntax_node1(x_42, x_43, x_7);
x_47 = l_Lean_Syntax_node2(x_42, x_32, x_34, x_46);
lean_inc(x_8);
x_48 = l_Lean_Syntax_node2(x_42, x_8, x_45, x_47);
x_16 = x_48;
goto block_21;
}
}
}
}
}
}
}
block_21:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_10, x_17);
x_19 = lean_array_uset(x_15, x_10, x_16);
x_10 = x_18;
x_11 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, size_t x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Command_addInheritDocDefault___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_addInheritDocDefault___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_addInheritDocDefault___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_addInheritDocDefault___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_addInheritDocDefault___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_addInheritDocDefault___closed__3;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_addInheritDocDefault___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attrInstance", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_addInheritDocDefault___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_addInheritDocDefault___closed__5;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_addInheritDocDefault___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addInheritDocDefault(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_6 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_7 = l_Lean_Elab_Command_addInheritDocDefault___closed__4;
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = l_Lean_Elab_Command_addInheritDocDefault___closed__6;
x_14 = l_Lean_Elab_Command_addInheritDocDefault___closed__7;
x_15 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg(x_4, x_5, x_6, x_9, x_8, x_1, x_13, x_16, x_17, x_15);
x_19 = l_Lean_Syntax_SepArray_ofElems(x_14, x_18);
lean_dec_ref(x_18);
lean_ctor_set(x_2, 0, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_20 = l_Lean_Elab_Command_addInheritDocDefault___closed__6;
x_21 = l_Lean_Elab_Command_addInheritDocDefault___closed__7;
x_22 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_23 = lean_array_size(x_22);
x_24 = 0;
x_25 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg(x_4, x_5, x_6, x_9, x_8, x_1, x_20, x_23, x_24, x_22);
x_26 = l_Lean_Syntax_SepArray_ofElems(x_21, x_25);
lean_dec_ref(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
lean_dec(x_1);
x_30 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
lean_inc(x_29);
x_31 = l_Lean_Syntax_isOfKind(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_2, 0);
lean_dec(x_33);
x_34 = lean_unsigned_to_nat(1u);
x_35 = l_Lean_Elab_Command_addInheritDocDefault___closed__6;
x_36 = l_Lean_Elab_Command_addInheritDocDefault___closed__7;
x_37 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_38 = lean_array_size(x_37);
x_39 = 0;
x_40 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg(x_28, x_4, x_5, x_6, x_34, x_30, x_29, x_35, x_38, x_39, x_37);
x_41 = l_Lean_Syntax_SepArray_ofElems(x_36, x_40);
lean_dec_ref(x_40);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l_Lean_Elab_Command_addInheritDocDefault___closed__6;
x_44 = l_Lean_Elab_Command_addInheritDocDefault___closed__7;
x_45 = l_Lean_Syntax_TSepArray_getElems___redArg(x_3);
lean_dec(x_3);
x_46 = lean_array_size(x_45);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg(x_28, x_4, x_5, x_6, x_42, x_30, x_29, x_43, x_46, x_47, x_45);
x_49 = l_Lean_Syntax_SepArray_ofElems(x_44, x_48);
lean_dec_ref(x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_5);
x_12 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_13 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_12, x_13, x_10);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_7);
x_14 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_15 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_14, x_15, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_13, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_15 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_16 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14, x_15, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Syntax", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precedence", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("identPrec", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("atom", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10;
lean_inc(x_1);
x_41 = l_Lean_Syntax_isOfKind(x_1, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12;
lean_inc(x_1);
x_43 = l_Lean_Syntax_isOfKind(x_1, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_44 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_2, 5);
lean_inc(x_45);
lean_dec_ref(x_2);
x_46 = l_Lean_SourceInfo_fromRef(x_45, x_41);
lean_dec(x_45);
x_47 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14;
x_48 = l_Lean_Syntax_node1(x_46, x_47, x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_3);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Syntax_getArg(x_1, x_50);
x_52 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
x_53 = l_Lean_Syntax_isOfKind(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_54 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = l_Lean_Syntax_getArg(x_1, x_55);
lean_dec(x_1);
x_57 = l_Lean_Syntax_isNone(x_56);
if (x_57 == 0)
{
uint8_t x_58; 
lean_inc(x_56);
x_58 = l_Lean_Syntax_matchesNull(x_56, x_55);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_56);
lean_dec_ref(x_2);
x_59 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = l_Lean_Syntax_getArg(x_56, x_50);
lean_dec(x_56);
x_61 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6;
lean_inc(x_60);
x_62 = l_Lean_Syntax_isOfKind(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_60);
lean_dec_ref(x_2);
x_63 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lean_Syntax_getArg(x_60, x_55);
lean_dec(x_60);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_16 = x_65;
x_17 = x_2;
x_18 = x_3;
goto block_39;
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_56);
x_66 = lean_box(0);
x_16 = x_66;
x_17 = x_2;
x_18 = x_3;
goto block_39;
}
}
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Array_append___redArg(x_9, x_10);
lean_dec_ref(x_10);
lean_inc(x_8);
x_12 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lean_Syntax_node2(x_8, x_5, x_7, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
block_39:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 5);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_21, x_22);
lean_dec(x_21);
x_24 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2;
x_25 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3;
x_26 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3;
x_27 = l_Lean_addMacroScope(x_19, x_26, x_20);
x_28 = lean_box(0);
lean_inc(x_23);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_31 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7;
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_32; 
x_32 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4;
x_4 = x_18;
x_5 = x_24;
x_6 = x_30;
x_7 = x_29;
x_8 = x_23;
x_9 = x_31;
x_10 = x_32;
goto block_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
lean_dec_ref(x_16);
x_34 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6;
x_35 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
lean_inc(x_23);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_23);
x_37 = l_Lean_Syntax_node2(x_23, x_34, x_36, x_33);
x_38 = l_Array_mkArray1___redArg(x_37);
x_4 = x_18;
x_5 = x_24;
x_6 = x_30;
x_7 = x_29;
x_8 = x_23;
x_9 = x_31;
x_10 = x_38;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_getKind(x_1);
x_4 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10;
x_5 = lean_name_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12;
x_7 = lean_name_eq(x_3, x_6);
lean_dec(x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Macro_throwUnsupported___redArg(x_2);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_strLitToPattern___redArg(x_1, x_2);
lean_dec(x_1);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_10 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l_Lean_Syntax_mkAntiquotNode(x_10, x_12, x_11, x_13, x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandNotationItemIntoPattern(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Syntax_getHeadInfo(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Syntax_getHeadInfo(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = l_Lean_Syntax_getTailInfo(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 3);
x_14 = lean_ctor_get(x_9, 2);
lean_dec(x_14);
x_15 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 2);
x_18 = lean_ctor_get(x_15, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
lean_ctor_set(x_15, 3, x_8);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 0, x_4);
x_21 = l_Lean_Syntax_setHeadInfo(x_2, x_15);
lean_ctor_set(x_9, 2, x_17);
x_22 = l_Lean_Syntax_setTailInfo(x_21, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_15, 2);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_7);
lean_ctor_set(x_24, 3, x_8);
x_25 = l_Lean_Syntax_setHeadInfo(x_2, x_24);
lean_ctor_set(x_9, 2, x_23);
x_26 = l_Lean_Syntax_setTailInfo(x_25, x_9);
return x_26;
}
}
else
{
lean_dec(x_15);
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_30 = l_Lean_Syntax_getTailInfo(x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc_ref(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 4, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_6);
lean_ctor_set(x_33, 2, x_7);
lean_ctor_set(x_33, 3, x_8);
x_34 = l_Lean_Syntax_setHeadInfo(x_2, x_33);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_29);
x_36 = l_Lean_Syntax_setTailInfo(x_34, x_35);
return x_36;
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_2;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
return x_2;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParenthesesAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_removeParenthesesAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
lean_inc_ref(x_4);
x_9 = l_Lean_Elab_Command_removeParentheses(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_15;
x_3 = x_16;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
}
static lean_object* _init_l_Lean_Elab_Command_removeParentheses___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_removeParentheses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_removeParentheses___closed__0;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_removeParentheses___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hygienicLParen", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_removeParentheses___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_removeParentheses___closed__2;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_removeParentheses___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_removeParentheses___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_removeParentheses___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeParentheses(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_removeParentheses___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_array_size(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_10, x_11, x_9, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 2, x_14);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_25 = lean_array_size(x_24);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_25, x_26, x_24, x_2, x_3);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_23);
lean_dec(x_22);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec_ref(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_getArg(x_1, x_38);
x_40 = l_Lean_Elab_Command_removeParentheses___closed__3;
lean_inc(x_39);
x_41 = l_Lean_Syntax_isOfKind(x_39, x_40);
if (x_41 == 0)
{
lean_dec(x_39);
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_1, 2);
x_46 = lean_array_size(x_45);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_46, x_47, x_45, x_2, x_3);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_1, 2, x_50);
lean_ctor_set(x_48, 0, x_1);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_48);
lean_ctor_set(x_1, 2, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_free_object(x_1);
lean_dec(x_44);
lean_dec(x_43);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_1, 0);
x_59 = lean_ctor_get(x_1, 1);
x_60 = lean_ctor_get(x_1, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_1);
x_61 = lean_array_size(x_60);
x_62 = 0;
x_63 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_61, x_62, x_60, x_2, x_3);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_59);
lean_dec(x_58);
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec_ref(x_2);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_3);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = l_Lean_Syntax_getArg(x_39, x_74);
lean_dec(x_39);
x_76 = l_Lean_Elab_Command_removeParentheses___closed__5;
lean_inc(x_75);
x_77 = l_Lean_Syntax_isOfKind(x_75, x_76);
if (x_77 == 0)
{
lean_dec(x_75);
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_1);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_1, 0);
x_80 = lean_ctor_get(x_1, 1);
x_81 = lean_ctor_get(x_1, 2);
x_82 = lean_array_size(x_81);
x_83 = 0;
x_84 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_82, x_83, x_81, x_2, x_3);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_ctor_set(x_1, 2, x_86);
lean_ctor_set(x_84, 0, x_1);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_84);
lean_ctor_set(x_1, 2, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_free_object(x_1);
lean_dec(x_80);
lean_dec(x_79);
x_90 = !lean_is_exclusive(x_84);
if (x_90 == 0)
{
return x_84;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_84, 0);
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_84);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
x_96 = lean_ctor_get(x_1, 2);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_97 = lean_array_size(x_96);
x_98 = 0;
x_99 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_97, x_98, x_96, x_2, x_3);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_94);
lean_ctor_set(x_103, 1, x_95);
lean_ctor_set(x_103, 2, x_100);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_95);
lean_dec(x_94);
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_107 = x_99;
} else {
 lean_dec_ref(x_99);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
lean_object* x_109; 
lean_dec_ref(x_2);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_3);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = l_Lean_Syntax_getArg(x_1, x_74);
x_111 = l_Lean_TSyntax_getHygieneInfo(x_75);
lean_dec(x_75);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
lean_inc_ref(x_2);
lean_inc(x_110);
x_113 = l_Lean_Elab_Term_expandCDot_x3f(x_110, x_112, x_2, x_3);
lean_dec_ref(x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
if (lean_obj_tag(x_114) == 0)
{
x_116 = x_110;
goto block_125;
}
else
{
lean_object* x_126; 
lean_dec(x_110);
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
lean_dec_ref(x_114);
x_116 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_117; 
x_117 = l_Lean_Elab_Command_removeParentheses(x_116, x_2, x_115);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = l_Lean_Elab_Command_removeParenthesesAux(x_1, x_119);
lean_dec(x_1);
lean_ctor_set(x_117, 0, x_120);
return x_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_117, 0);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_117);
x_123 = l_Lean_Elab_Command_removeParenthesesAux(x_1, x_121);
lean_dec(x_1);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_dec(x_1);
return x_117;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_110);
lean_dec_ref(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_113);
if (x_127 == 0)
{
return x_113;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_113, 0);
x_129 = lean_ctor_get(x_113, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_113);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_8, x_7);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_array_uget(x_6, x_8);
lean_inc(x_12);
lean_inc(x_1);
x_15 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_2, x_3, x_14, x_12, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_12);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_5);
x_18 = 1;
x_19 = lean_usize_add(x_8, x_18);
x_8 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_array_uget(x_6, x_8);
lean_inc(x_21);
lean_inc(x_1);
x_23 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_2, x_3, x_22, x_21, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec_ref(x_23);
lean_inc(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
x_28 = 1;
x_29 = lean_usize_add(x_8, x_28);
x_8 = x_29;
x_9 = x_27;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("choice", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_19; lean_object* x_20; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_5, 1);
x_33 = lean_ctor_get(x_5, 0);
lean_dec(x_33);
x_34 = l_Lean_Syntax_isAntiquot(x_4);
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
lean_inc_ref(x_5);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_5);
x_19 = x_35;
x_20 = x_5;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Lean_Syntax_getAntiquotTerm(x_4);
x_37 = l_Lean_Syntax_getId(x_36);
lean_dec(x_36);
x_38 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_37, x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_NameSet_insert(x_32, x_37);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_1);
lean_inc_ref(x_5);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_5);
x_19 = x_40;
x_20 = x_5;
goto block_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_1);
x_41 = lean_box(x_2);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_5, 0, x_42);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_5);
return x_43;
}
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_dec(x_5);
x_45 = l_Lean_Syntax_isAntiquot(x_4);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_inc(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_44);
lean_inc_ref(x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_19 = x_47;
x_20 = x_46;
goto block_30;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = l_Lean_Syntax_getAntiquotTerm(x_4);
x_49 = l_Lean_Syntax_getId(x_48);
lean_dec(x_48);
x_50 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_49, x_44);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = l_Lean_NameSet_insert(x_44, x_49);
lean_inc(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_51);
lean_inc_ref(x_52);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_19 = x_53;
x_20 = x_52;
goto block_30;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_4);
lean_dec(x_1);
x_54 = lean_box(x_2);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_44);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
block_18:
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_array_size(x_7);
x_12 = 0;
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(x_1, x_2, x_3, x_6, x_9, x_7, x_11, x_12, x_10);
lean_dec_ref(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
return x_17;
}
}
block_30:
{
if (lean_obj_tag(x_4) == 1)
{
lean_dec_ref(x_19);
if (x_3 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_4);
x_7 = x_21;
x_8 = x_20;
goto block_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_4);
x_24 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1;
x_25 = lean_name_eq(x_22, x_24);
lean_dec(x_22);
if (x_25 == 0)
{
x_7 = x_23;
x_8 = x_20;
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_box(0);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get(x_26, x_23, x_27);
lean_dec_ref(x_23);
x_4 = x_28;
x_5 = x_20;
goto _start;
}
}
}
else
{
lean_dec_ref(x_20);
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_4, x_3);
if (x_23 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_26 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
lean_inc_ref(x_5);
lean_inc(x_1);
x_27 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_23, x_23, x_26, x_5, x_5);
lean_dec_ref(x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_6 = x_28;
goto block_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_29);
lean_inc_ref(x_31);
lean_inc(x_1);
x_32 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_23, x_23, x_30, x_31, x_31);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_6 = x_33;
goto block_22;
}
}
block_22:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_inc(x_1);
lean_ctor_set(x_6, 0, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_5 = x_6;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
lean_inc(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_4, x_3);
if (x_23 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_26 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
lean_inc_ref(x_5);
lean_inc(x_1);
x_27 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_23, x_23, x_26, x_5, x_5);
lean_dec_ref(x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_6 = x_28;
goto block_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_29);
lean_inc_ref(x_31);
lean_inc(x_1);
x_32 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_23, x_23, x_30, x_31, x_31);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_6 = x_33;
goto block_22;
}
}
block_22:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_inc(x_1);
lean_ctor_set(x_6, 0, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2(x_1, x_2, x_3, x_11, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
lean_inc(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2(x_1, x_2, x_3, x_16, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_hasDuplicateAntiquot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0;
x_4 = lean_array_size(x_1);
x_5 = 0;
x_6 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2(x_2, x_1, x_4, x_5, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_12, x_13, x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("antiquot", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__0;
x_2 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("$", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("f", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__3;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("antiquotName", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("aux_def", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__9;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_3 = l_Lean_Elab_Command_mkUnexpander___closed__8;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attributes", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__11;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__2;
x_2 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__1;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app_unexpander", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__15;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpand", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__19;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__19;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.PrettyPrinter.Unexpander", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__22;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpander", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__25;
x_2 = l_Lean_Elab_Command_mkUnexpander___closed__24;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":=", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fun", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__28;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchAlts", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__30;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchAlt", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__32;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("|", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quot", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__35;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`(", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=>", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withRef", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__40;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__40;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__40;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__44;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throw", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__47;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__47;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MonadExcept", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__47;
x_2 = l_Lean_Elab_Command_mkUnexpander___closed__50;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tuple", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__52;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__55() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__55;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_2 = l_Lean_Elab_Command_mkUnexpander___closed__8;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__57;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__59;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__61;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__63;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkUnexpander___closed__64;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__65;
x_2 = l_Lean_Elab_Command_mkUnexpander___closed__62;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__66;
x_2 = l_Lean_Elab_Command_mkUnexpander___closed__60;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkUnexpander___closed__67;
x_2 = l_Lean_Elab_Command_mkUnexpander___closed__58;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkUnexpander___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkUnexpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_560; uint8_t x_561; 
x_560 = l_Lean_Elab_Command_addInheritDocDefault___closed__4;
lean_inc(x_3);
x_561 = l_Lean_Syntax_isOfKind(x_3, x_560);
if (x_561 == 0)
{
lean_object* x_562; uint8_t x_563; 
x_562 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
lean_inc(x_3);
x_563 = l_Lean_Syntax_isOfKind(x_3, x_562);
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_564 = lean_box(0);
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_5);
return x_565;
}
else
{
lean_object* x_566; 
x_566 = l_Lean_Elab_Command_mkUnexpander___closed__69;
x_10 = x_3;
x_11 = x_566;
x_12 = x_4;
x_13 = x_5;
goto block_559;
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; 
x_567 = lean_unsigned_to_nat(0u);
x_568 = l_Lean_Syntax_getArg(x_3, x_567);
x_569 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
lean_inc(x_568);
x_570 = l_Lean_Syntax_isOfKind(x_568, x_569);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; 
lean_dec(x_568);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_571 = lean_box(0);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_5);
return x_572;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_unsigned_to_nat(1u);
x_574 = l_Lean_Syntax_getArg(x_3, x_573);
lean_dec(x_3);
x_575 = l_Lean_Syntax_getArgs(x_574);
lean_dec(x_574);
x_10 = x_568;
x_11 = x_575;
x_12 = x_4;
x_13 = x_5;
goto block_559;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_559:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Syntax_getId(x_10);
lean_dec(x_10);
lean_inc_ref(x_12);
x_15 = l_Lean_Macro_resolveGlobalName(x_14, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_6 = x_17;
goto block_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 1);
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec_ref(x_15);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_dec(x_26);
x_27 = lean_array_size(x_11);
x_28 = 0;
lean_inc_ref(x_12);
x_29 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_27, x_28, x_11, x_12, x_23);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_12, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 5);
lean_inc(x_35);
lean_dec_ref(x_12);
x_36 = l_Lean_SourceInfo_fromRef(x_35, x_32);
lean_dec(x_35);
x_37 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0;
x_38 = l_Lean_Elab_Command_mkUnexpander___closed__1;
x_39 = l_Lean_Elab_Command_mkUnexpander___closed__2;
lean_inc(x_36);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_39);
lean_ctor_set(x_18, 0, x_36);
x_40 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_41 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7;
lean_inc(x_36);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = l_Lean_Elab_Command_mkUnexpander___closed__4;
x_44 = l_Lean_Elab_Command_mkUnexpander___closed__5;
lean_inc(x_34);
lean_inc(x_33);
x_45 = l_Lean_addMacroScope(x_33, x_44, x_34);
x_46 = lean_box(0);
lean_inc(x_36);
x_47 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_46);
x_48 = l_Lean_Elab_Command_mkUnexpander___closed__7;
x_49 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
lean_inc(x_36);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_36);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_37);
lean_inc_ref(x_50);
lean_inc(x_36);
x_52 = l_Lean_Syntax_node2(x_36, x_48, x_50, x_51);
lean_inc_ref(x_47);
lean_inc_ref(x_42);
lean_inc(x_36);
x_53 = l_Lean_Syntax_node4(x_36, x_38, x_18, x_42, x_47, x_52);
x_54 = l_Lean_Syntax_mkApp(x_53, x_31);
x_55 = l_Lean_Elab_Command_mkUnexpander___closed__9;
x_56 = l_Lean_Elab_Command_mkUnexpander___closed__10;
x_57 = l_Lean_Elab_Command_mkUnexpander___closed__12;
x_58 = l_Lean_Elab_Command_mkUnexpander___closed__13;
lean_inc(x_36);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_36);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Command_addInheritDocDefault___closed__6;
x_61 = l_Lean_Elab_Command_mkUnexpander___closed__14;
x_62 = l_Lean_Elab_Command_mkUnexpander___closed__16;
x_63 = l_Lean_Elab_Command_mkUnexpander___closed__17;
lean_inc(x_34);
lean_inc(x_33);
x_64 = l_Lean_addMacroScope(x_33, x_63, x_34);
lean_inc(x_36);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_36);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_46);
x_66 = lean_mk_syntax_ident(x_25);
lean_inc(x_66);
lean_inc(x_36);
x_67 = l_Lean_Syntax_node1(x_36, x_40, x_66);
lean_inc(x_36);
x_68 = l_Lean_Syntax_node2(x_36, x_61, x_65, x_67);
lean_inc(x_36);
x_69 = l_Lean_Syntax_node2(x_36, x_60, x_1, x_68);
lean_inc(x_36);
x_70 = l_Lean_Syntax_node1(x_36, x_40, x_69);
x_71 = l_Lean_Elab_Command_mkUnexpander___closed__18;
lean_inc(x_36);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_36);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_36);
x_73 = l_Lean_Syntax_node3(x_36, x_57, x_59, x_70, x_72);
lean_inc(x_36);
x_74 = l_Lean_Syntax_node1(x_36, x_40, x_73);
lean_inc(x_36);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_36);
lean_ctor_set(x_75, 1, x_55);
x_76 = l_Lean_Elab_Command_mkUnexpander___closed__20;
x_77 = l_Lean_Elab_Command_mkUnexpander___closed__21;
lean_inc(x_34);
lean_inc(x_33);
x_78 = l_Lean_addMacroScope(x_33, x_77, x_34);
lean_inc(x_36);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_36);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_46);
lean_inc(x_36);
x_80 = l_Lean_Syntax_node2(x_36, x_40, x_79, x_66);
x_81 = l_Lean_Elab_Command_mkUnexpander___closed__23;
x_82 = l_Lean_Elab_Command_mkUnexpander___closed__26;
lean_inc(x_34);
lean_inc(x_33);
x_83 = l_Lean_addMacroScope(x_33, x_82, x_34);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_19);
lean_ctor_set(x_16, 1, x_46);
lean_ctor_set(x_16, 0, x_84);
lean_inc(x_36);
x_85 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_85, 0, x_36);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_83);
lean_ctor_set(x_85, 3, x_16);
x_86 = l_Lean_Elab_Command_mkUnexpander___closed__27;
lean_inc(x_36);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_36);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Elab_Command_mkUnexpander___closed__28;
x_89 = l_Lean_Elab_Command_mkUnexpander___closed__29;
lean_inc(x_36);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_36);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_Elab_Command_mkUnexpander___closed__31;
x_92 = l_Lean_Elab_Command_mkUnexpander___closed__33;
x_93 = l_Lean_Elab_Command_mkUnexpander___closed__34;
lean_inc(x_36);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_36);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Elab_Command_mkUnexpander___closed__36;
x_96 = l_Lean_Elab_Command_mkUnexpander___closed__37;
lean_inc(x_36);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_36);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Elab_Command_mkUnexpander___closed__38;
lean_inc(x_36);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_36);
lean_ctor_set(x_99, 1, x_98);
lean_inc_ref(x_99);
lean_inc_ref(x_97);
lean_inc(x_36);
x_100 = l_Lean_Syntax_node3(x_36, x_95, x_97, x_54, x_99);
lean_inc(x_36);
x_101 = l_Lean_Syntax_node1(x_36, x_40, x_100);
lean_inc(x_36);
x_102 = l_Lean_Syntax_node1(x_36, x_40, x_101);
x_103 = l_Lean_Elab_Command_mkUnexpander___closed__39;
lean_inc(x_36);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_36);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_Elab_Command_addInheritDocDefault___closed__4;
x_106 = l_Lean_Elab_Command_mkUnexpander___closed__41;
x_107 = l_Lean_Elab_Command_mkUnexpander___closed__42;
lean_inc(x_34);
lean_inc(x_33);
x_108 = l_Lean_addMacroScope(x_33, x_107, x_34);
x_109 = l_Lean_Elab_Command_mkUnexpander___closed__43;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_19);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_46);
lean_inc(x_36);
x_112 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_112, 0, x_36);
lean_ctor_set(x_112, 1, x_106);
lean_ctor_set(x_112, 2, x_108);
lean_ctor_set(x_112, 3, x_111);
lean_inc_ref(x_99);
lean_inc(x_36);
x_113 = l_Lean_Syntax_node3(x_36, x_95, x_97, x_2, x_99);
lean_inc(x_36);
x_114 = l_Lean_Syntax_node2(x_36, x_40, x_47, x_113);
lean_inc(x_36);
x_115 = l_Lean_Syntax_node2(x_36, x_105, x_112, x_114);
lean_inc_ref(x_104);
lean_inc_ref(x_94);
lean_inc(x_36);
x_116 = l_Lean_Syntax_node4(x_36, x_92, x_94, x_102, x_104, x_115);
x_117 = l_Lean_Elab_Command_mkUnexpander___closed__45;
x_118 = l_Lean_Elab_Command_mkUnexpander___closed__46;
lean_inc(x_36);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_36);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_36);
x_120 = l_Lean_Syntax_node1(x_36, x_117, x_119);
lean_inc(x_36);
x_121 = l_Lean_Syntax_node1(x_36, x_40, x_120);
lean_inc(x_36);
x_122 = l_Lean_Syntax_node1(x_36, x_40, x_121);
x_123 = l_Lean_Elab_Command_mkUnexpander___closed__48;
x_124 = l_Lean_Elab_Command_mkUnexpander___closed__49;
lean_inc(x_34);
lean_inc(x_33);
x_125 = l_Lean_addMacroScope(x_33, x_124, x_34);
x_126 = l_Lean_Elab_Command_mkUnexpander___closed__51;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_19);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_46);
lean_inc(x_36);
x_129 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_129, 0, x_36);
lean_ctor_set(x_129, 1, x_123);
lean_ctor_set(x_129, 2, x_125);
lean_ctor_set(x_129, 3, x_128);
x_130 = l_Lean_Elab_Command_mkUnexpander___closed__53;
x_131 = l_Lean_Elab_Command_removeParentheses___closed__3;
x_132 = l_Lean_Elab_Command_mkUnexpander___closed__54;
lean_inc(x_36);
x_133 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_133, 0, x_36);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Elab_Command_removeParentheses___closed__5;
x_135 = l_Lean_Elab_Command_mkUnexpander___closed__56;
x_136 = lean_box(0);
x_137 = l_Lean_addMacroScope(x_33, x_136, x_34);
x_138 = l_Lean_Elab_Command_mkUnexpander___closed__68;
lean_inc(x_36);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_36);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_138);
lean_inc(x_36);
x_140 = l_Lean_Syntax_node1(x_36, x_134, x_139);
lean_inc(x_36);
x_141 = l_Lean_Syntax_node2(x_36, x_131, x_133, x_140);
lean_inc_ref(x_42);
lean_inc(x_36);
x_142 = l_Lean_Syntax_node3(x_36, x_130, x_141, x_42, x_99);
lean_inc(x_36);
x_143 = l_Lean_Syntax_node1(x_36, x_40, x_142);
lean_inc(x_36);
x_144 = l_Lean_Syntax_node2(x_36, x_105, x_129, x_143);
lean_inc(x_36);
x_145 = l_Lean_Syntax_node4(x_36, x_92, x_94, x_122, x_104, x_144);
lean_inc(x_36);
x_146 = l_Lean_Syntax_node2(x_36, x_40, x_116, x_145);
lean_inc(x_36);
x_147 = l_Lean_Syntax_node1(x_36, x_91, x_146);
lean_inc(x_36);
x_148 = l_Lean_Syntax_node2(x_36, x_89, x_90, x_147);
x_149 = l_Lean_Syntax_node8(x_36, x_56, x_42, x_74, x_75, x_80, x_50, x_85, x_87, x_148);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_29, 0, x_150);
return x_29;
}
else
{
lean_object* x_151; 
lean_dec(x_31);
lean_free_object(x_18);
lean_dec(x_25);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_151 = lean_box(0);
lean_ctor_set(x_29, 0, x_151);
return x_29;
}
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_29, 0);
x_153 = lean_ctor_get(x_29, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_29);
x_154 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_155 = lean_ctor_get(x_12, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_12, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_12, 5);
lean_inc(x_157);
lean_dec_ref(x_12);
x_158 = l_Lean_SourceInfo_fromRef(x_157, x_154);
lean_dec(x_157);
x_159 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0;
x_160 = l_Lean_Elab_Command_mkUnexpander___closed__1;
x_161 = l_Lean_Elab_Command_mkUnexpander___closed__2;
lean_inc(x_158);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_161);
lean_ctor_set(x_18, 0, x_158);
x_162 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_163 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7;
lean_inc(x_158);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_163);
x_165 = l_Lean_Elab_Command_mkUnexpander___closed__4;
x_166 = l_Lean_Elab_Command_mkUnexpander___closed__5;
lean_inc(x_156);
lean_inc(x_155);
x_167 = l_Lean_addMacroScope(x_155, x_166, x_156);
x_168 = lean_box(0);
lean_inc(x_158);
x_169 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_169, 0, x_158);
lean_ctor_set(x_169, 1, x_165);
lean_ctor_set(x_169, 2, x_167);
lean_ctor_set(x_169, 3, x_168);
x_170 = l_Lean_Elab_Command_mkUnexpander___closed__7;
x_171 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
lean_inc(x_158);
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_158);
lean_ctor_set(x_172, 1, x_171);
lean_inc(x_158);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_158);
lean_ctor_set(x_173, 1, x_159);
lean_inc_ref(x_172);
lean_inc(x_158);
x_174 = l_Lean_Syntax_node2(x_158, x_170, x_172, x_173);
lean_inc_ref(x_169);
lean_inc_ref(x_164);
lean_inc(x_158);
x_175 = l_Lean_Syntax_node4(x_158, x_160, x_18, x_164, x_169, x_174);
x_176 = l_Lean_Syntax_mkApp(x_175, x_152);
x_177 = l_Lean_Elab_Command_mkUnexpander___closed__9;
x_178 = l_Lean_Elab_Command_mkUnexpander___closed__10;
x_179 = l_Lean_Elab_Command_mkUnexpander___closed__12;
x_180 = l_Lean_Elab_Command_mkUnexpander___closed__13;
lean_inc(x_158);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_158);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Elab_Command_addInheritDocDefault___closed__6;
x_183 = l_Lean_Elab_Command_mkUnexpander___closed__14;
x_184 = l_Lean_Elab_Command_mkUnexpander___closed__16;
x_185 = l_Lean_Elab_Command_mkUnexpander___closed__17;
lean_inc(x_156);
lean_inc(x_155);
x_186 = l_Lean_addMacroScope(x_155, x_185, x_156);
lean_inc(x_158);
x_187 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_187, 0, x_158);
lean_ctor_set(x_187, 1, x_184);
lean_ctor_set(x_187, 2, x_186);
lean_ctor_set(x_187, 3, x_168);
x_188 = lean_mk_syntax_ident(x_25);
lean_inc(x_188);
lean_inc(x_158);
x_189 = l_Lean_Syntax_node1(x_158, x_162, x_188);
lean_inc(x_158);
x_190 = l_Lean_Syntax_node2(x_158, x_183, x_187, x_189);
lean_inc(x_158);
x_191 = l_Lean_Syntax_node2(x_158, x_182, x_1, x_190);
lean_inc(x_158);
x_192 = l_Lean_Syntax_node1(x_158, x_162, x_191);
x_193 = l_Lean_Elab_Command_mkUnexpander___closed__18;
lean_inc(x_158);
x_194 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_194, 0, x_158);
lean_ctor_set(x_194, 1, x_193);
lean_inc(x_158);
x_195 = l_Lean_Syntax_node3(x_158, x_179, x_181, x_192, x_194);
lean_inc(x_158);
x_196 = l_Lean_Syntax_node1(x_158, x_162, x_195);
lean_inc(x_158);
x_197 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_197, 0, x_158);
lean_ctor_set(x_197, 1, x_177);
x_198 = l_Lean_Elab_Command_mkUnexpander___closed__20;
x_199 = l_Lean_Elab_Command_mkUnexpander___closed__21;
lean_inc(x_156);
lean_inc(x_155);
x_200 = l_Lean_addMacroScope(x_155, x_199, x_156);
lean_inc(x_158);
x_201 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_201, 0, x_158);
lean_ctor_set(x_201, 1, x_198);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_168);
lean_inc(x_158);
x_202 = l_Lean_Syntax_node2(x_158, x_162, x_201, x_188);
x_203 = l_Lean_Elab_Command_mkUnexpander___closed__23;
x_204 = l_Lean_Elab_Command_mkUnexpander___closed__26;
lean_inc(x_156);
lean_inc(x_155);
x_205 = l_Lean_addMacroScope(x_155, x_204, x_156);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_19);
lean_ctor_set(x_16, 1, x_168);
lean_ctor_set(x_16, 0, x_206);
lean_inc(x_158);
x_207 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_207, 0, x_158);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_205);
lean_ctor_set(x_207, 3, x_16);
x_208 = l_Lean_Elab_Command_mkUnexpander___closed__27;
lean_inc(x_158);
x_209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_209, 0, x_158);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_Elab_Command_mkUnexpander___closed__28;
x_211 = l_Lean_Elab_Command_mkUnexpander___closed__29;
lean_inc(x_158);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_158);
lean_ctor_set(x_212, 1, x_210);
x_213 = l_Lean_Elab_Command_mkUnexpander___closed__31;
x_214 = l_Lean_Elab_Command_mkUnexpander___closed__33;
x_215 = l_Lean_Elab_Command_mkUnexpander___closed__34;
lean_inc(x_158);
x_216 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_216, 0, x_158);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_Elab_Command_mkUnexpander___closed__36;
x_218 = l_Lean_Elab_Command_mkUnexpander___closed__37;
lean_inc(x_158);
x_219 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_219, 0, x_158);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_Elab_Command_mkUnexpander___closed__38;
lean_inc(x_158);
x_221 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_221, 0, x_158);
lean_ctor_set(x_221, 1, x_220);
lean_inc_ref(x_221);
lean_inc_ref(x_219);
lean_inc(x_158);
x_222 = l_Lean_Syntax_node3(x_158, x_217, x_219, x_176, x_221);
lean_inc(x_158);
x_223 = l_Lean_Syntax_node1(x_158, x_162, x_222);
lean_inc(x_158);
x_224 = l_Lean_Syntax_node1(x_158, x_162, x_223);
x_225 = l_Lean_Elab_Command_mkUnexpander___closed__39;
lean_inc(x_158);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_158);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_Elab_Command_addInheritDocDefault___closed__4;
x_228 = l_Lean_Elab_Command_mkUnexpander___closed__41;
x_229 = l_Lean_Elab_Command_mkUnexpander___closed__42;
lean_inc(x_156);
lean_inc(x_155);
x_230 = l_Lean_addMacroScope(x_155, x_229, x_156);
x_231 = l_Lean_Elab_Command_mkUnexpander___closed__43;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_19);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_168);
lean_inc(x_158);
x_234 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_234, 0, x_158);
lean_ctor_set(x_234, 1, x_228);
lean_ctor_set(x_234, 2, x_230);
lean_ctor_set(x_234, 3, x_233);
lean_inc_ref(x_221);
lean_inc(x_158);
x_235 = l_Lean_Syntax_node3(x_158, x_217, x_219, x_2, x_221);
lean_inc(x_158);
x_236 = l_Lean_Syntax_node2(x_158, x_162, x_169, x_235);
lean_inc(x_158);
x_237 = l_Lean_Syntax_node2(x_158, x_227, x_234, x_236);
lean_inc_ref(x_226);
lean_inc_ref(x_216);
lean_inc(x_158);
x_238 = l_Lean_Syntax_node4(x_158, x_214, x_216, x_224, x_226, x_237);
x_239 = l_Lean_Elab_Command_mkUnexpander___closed__45;
x_240 = l_Lean_Elab_Command_mkUnexpander___closed__46;
lean_inc(x_158);
x_241 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_241, 0, x_158);
lean_ctor_set(x_241, 1, x_240);
lean_inc(x_158);
x_242 = l_Lean_Syntax_node1(x_158, x_239, x_241);
lean_inc(x_158);
x_243 = l_Lean_Syntax_node1(x_158, x_162, x_242);
lean_inc(x_158);
x_244 = l_Lean_Syntax_node1(x_158, x_162, x_243);
x_245 = l_Lean_Elab_Command_mkUnexpander___closed__48;
x_246 = l_Lean_Elab_Command_mkUnexpander___closed__49;
lean_inc(x_156);
lean_inc(x_155);
x_247 = l_Lean_addMacroScope(x_155, x_246, x_156);
x_248 = l_Lean_Elab_Command_mkUnexpander___closed__51;
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_19);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_168);
lean_inc(x_158);
x_251 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_251, 0, x_158);
lean_ctor_set(x_251, 1, x_245);
lean_ctor_set(x_251, 2, x_247);
lean_ctor_set(x_251, 3, x_250);
x_252 = l_Lean_Elab_Command_mkUnexpander___closed__53;
x_253 = l_Lean_Elab_Command_removeParentheses___closed__3;
x_254 = l_Lean_Elab_Command_mkUnexpander___closed__54;
lean_inc(x_158);
x_255 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_255, 0, x_158);
lean_ctor_set(x_255, 1, x_254);
x_256 = l_Lean_Elab_Command_removeParentheses___closed__5;
x_257 = l_Lean_Elab_Command_mkUnexpander___closed__56;
x_258 = lean_box(0);
x_259 = l_Lean_addMacroScope(x_155, x_258, x_156);
x_260 = l_Lean_Elab_Command_mkUnexpander___closed__68;
lean_inc(x_158);
x_261 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_261, 0, x_158);
lean_ctor_set(x_261, 1, x_257);
lean_ctor_set(x_261, 2, x_259);
lean_ctor_set(x_261, 3, x_260);
lean_inc(x_158);
x_262 = l_Lean_Syntax_node1(x_158, x_256, x_261);
lean_inc(x_158);
x_263 = l_Lean_Syntax_node2(x_158, x_253, x_255, x_262);
lean_inc_ref(x_164);
lean_inc(x_158);
x_264 = l_Lean_Syntax_node3(x_158, x_252, x_263, x_164, x_221);
lean_inc(x_158);
x_265 = l_Lean_Syntax_node1(x_158, x_162, x_264);
lean_inc(x_158);
x_266 = l_Lean_Syntax_node2(x_158, x_227, x_251, x_265);
lean_inc(x_158);
x_267 = l_Lean_Syntax_node4(x_158, x_214, x_216, x_244, x_226, x_266);
lean_inc(x_158);
x_268 = l_Lean_Syntax_node2(x_158, x_162, x_238, x_267);
lean_inc(x_158);
x_269 = l_Lean_Syntax_node1(x_158, x_213, x_268);
lean_inc(x_158);
x_270 = l_Lean_Syntax_node2(x_158, x_211, x_212, x_269);
x_271 = l_Lean_Syntax_node8(x_158, x_178, x_164, x_196, x_197, x_202, x_172, x_207, x_209, x_270);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_271);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_153);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_152);
lean_free_object(x_18);
lean_dec(x_25);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_274 = lean_box(0);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_153);
return x_275;
}
}
}
else
{
uint8_t x_276; 
lean_free_object(x_18);
lean_dec(x_25);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_29);
if (x_276 == 0)
{
return x_29;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_29, 0);
x_278 = lean_ctor_get(x_29, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_29);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
lean_object* x_280; size_t x_281; size_t x_282; lean_object* x_283; 
x_280 = lean_ctor_get(x_18, 0);
lean_inc(x_280);
lean_dec(x_18);
x_281 = lean_array_size(x_11);
x_282 = 0;
lean_inc_ref(x_12);
x_283 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_281, x_282, x_11, x_12, x_23);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_286 = x_283;
} else {
 lean_dec_ref(x_283);
 x_286 = lean_box(0);
}
x_287 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_284);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_288 = lean_ctor_get(x_12, 1);
lean_inc(x_288);
x_289 = lean_ctor_get(x_12, 2);
lean_inc(x_289);
x_290 = lean_ctor_get(x_12, 5);
lean_inc(x_290);
lean_dec_ref(x_12);
x_291 = l_Lean_SourceInfo_fromRef(x_290, x_287);
lean_dec(x_290);
x_292 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0;
x_293 = l_Lean_Elab_Command_mkUnexpander___closed__1;
x_294 = l_Lean_Elab_Command_mkUnexpander___closed__2;
lean_inc(x_291);
x_295 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_295, 0, x_291);
lean_ctor_set(x_295, 1, x_294);
x_296 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_297 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7;
lean_inc(x_291);
x_298 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_298, 0, x_291);
lean_ctor_set(x_298, 1, x_296);
lean_ctor_set(x_298, 2, x_297);
x_299 = l_Lean_Elab_Command_mkUnexpander___closed__4;
x_300 = l_Lean_Elab_Command_mkUnexpander___closed__5;
lean_inc(x_289);
lean_inc(x_288);
x_301 = l_Lean_addMacroScope(x_288, x_300, x_289);
x_302 = lean_box(0);
lean_inc(x_291);
x_303 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_303, 0, x_291);
lean_ctor_set(x_303, 1, x_299);
lean_ctor_set(x_303, 2, x_301);
lean_ctor_set(x_303, 3, x_302);
x_304 = l_Lean_Elab_Command_mkUnexpander___closed__7;
x_305 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
lean_inc(x_291);
x_306 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_306, 0, x_291);
lean_ctor_set(x_306, 1, x_305);
lean_inc(x_291);
x_307 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_307, 0, x_291);
lean_ctor_set(x_307, 1, x_292);
lean_inc_ref(x_306);
lean_inc(x_291);
x_308 = l_Lean_Syntax_node2(x_291, x_304, x_306, x_307);
lean_inc_ref(x_303);
lean_inc_ref(x_298);
lean_inc(x_291);
x_309 = l_Lean_Syntax_node4(x_291, x_293, x_295, x_298, x_303, x_308);
x_310 = l_Lean_Syntax_mkApp(x_309, x_284);
x_311 = l_Lean_Elab_Command_mkUnexpander___closed__9;
x_312 = l_Lean_Elab_Command_mkUnexpander___closed__10;
x_313 = l_Lean_Elab_Command_mkUnexpander___closed__12;
x_314 = l_Lean_Elab_Command_mkUnexpander___closed__13;
lean_inc(x_291);
x_315 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_315, 0, x_291);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_Lean_Elab_Command_addInheritDocDefault___closed__6;
x_317 = l_Lean_Elab_Command_mkUnexpander___closed__14;
x_318 = l_Lean_Elab_Command_mkUnexpander___closed__16;
x_319 = l_Lean_Elab_Command_mkUnexpander___closed__17;
lean_inc(x_289);
lean_inc(x_288);
x_320 = l_Lean_addMacroScope(x_288, x_319, x_289);
lean_inc(x_291);
x_321 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_321, 0, x_291);
lean_ctor_set(x_321, 1, x_318);
lean_ctor_set(x_321, 2, x_320);
lean_ctor_set(x_321, 3, x_302);
x_322 = lean_mk_syntax_ident(x_280);
lean_inc(x_322);
lean_inc(x_291);
x_323 = l_Lean_Syntax_node1(x_291, x_296, x_322);
lean_inc(x_291);
x_324 = l_Lean_Syntax_node2(x_291, x_317, x_321, x_323);
lean_inc(x_291);
x_325 = l_Lean_Syntax_node2(x_291, x_316, x_1, x_324);
lean_inc(x_291);
x_326 = l_Lean_Syntax_node1(x_291, x_296, x_325);
x_327 = l_Lean_Elab_Command_mkUnexpander___closed__18;
lean_inc(x_291);
x_328 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_328, 0, x_291);
lean_ctor_set(x_328, 1, x_327);
lean_inc(x_291);
x_329 = l_Lean_Syntax_node3(x_291, x_313, x_315, x_326, x_328);
lean_inc(x_291);
x_330 = l_Lean_Syntax_node1(x_291, x_296, x_329);
lean_inc(x_291);
x_331 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_331, 0, x_291);
lean_ctor_set(x_331, 1, x_311);
x_332 = l_Lean_Elab_Command_mkUnexpander___closed__20;
x_333 = l_Lean_Elab_Command_mkUnexpander___closed__21;
lean_inc(x_289);
lean_inc(x_288);
x_334 = l_Lean_addMacroScope(x_288, x_333, x_289);
lean_inc(x_291);
x_335 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_335, 0, x_291);
lean_ctor_set(x_335, 1, x_332);
lean_ctor_set(x_335, 2, x_334);
lean_ctor_set(x_335, 3, x_302);
lean_inc(x_291);
x_336 = l_Lean_Syntax_node2(x_291, x_296, x_335, x_322);
x_337 = l_Lean_Elab_Command_mkUnexpander___closed__23;
x_338 = l_Lean_Elab_Command_mkUnexpander___closed__26;
lean_inc(x_289);
lean_inc(x_288);
x_339 = l_Lean_addMacroScope(x_288, x_338, x_289);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_19);
lean_ctor_set(x_16, 1, x_302);
lean_ctor_set(x_16, 0, x_340);
lean_inc(x_291);
x_341 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_341, 0, x_291);
lean_ctor_set(x_341, 1, x_337);
lean_ctor_set(x_341, 2, x_339);
lean_ctor_set(x_341, 3, x_16);
x_342 = l_Lean_Elab_Command_mkUnexpander___closed__27;
lean_inc(x_291);
x_343 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_343, 0, x_291);
lean_ctor_set(x_343, 1, x_342);
x_344 = l_Lean_Elab_Command_mkUnexpander___closed__28;
x_345 = l_Lean_Elab_Command_mkUnexpander___closed__29;
lean_inc(x_291);
x_346 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_346, 0, x_291);
lean_ctor_set(x_346, 1, x_344);
x_347 = l_Lean_Elab_Command_mkUnexpander___closed__31;
x_348 = l_Lean_Elab_Command_mkUnexpander___closed__33;
x_349 = l_Lean_Elab_Command_mkUnexpander___closed__34;
lean_inc(x_291);
x_350 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_350, 0, x_291);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Lean_Elab_Command_mkUnexpander___closed__36;
x_352 = l_Lean_Elab_Command_mkUnexpander___closed__37;
lean_inc(x_291);
x_353 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_353, 0, x_291);
lean_ctor_set(x_353, 1, x_352);
x_354 = l_Lean_Elab_Command_mkUnexpander___closed__38;
lean_inc(x_291);
x_355 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_355, 0, x_291);
lean_ctor_set(x_355, 1, x_354);
lean_inc_ref(x_355);
lean_inc_ref(x_353);
lean_inc(x_291);
x_356 = l_Lean_Syntax_node3(x_291, x_351, x_353, x_310, x_355);
lean_inc(x_291);
x_357 = l_Lean_Syntax_node1(x_291, x_296, x_356);
lean_inc(x_291);
x_358 = l_Lean_Syntax_node1(x_291, x_296, x_357);
x_359 = l_Lean_Elab_Command_mkUnexpander___closed__39;
lean_inc(x_291);
x_360 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_360, 0, x_291);
lean_ctor_set(x_360, 1, x_359);
x_361 = l_Lean_Elab_Command_addInheritDocDefault___closed__4;
x_362 = l_Lean_Elab_Command_mkUnexpander___closed__41;
x_363 = l_Lean_Elab_Command_mkUnexpander___closed__42;
lean_inc(x_289);
lean_inc(x_288);
x_364 = l_Lean_addMacroScope(x_288, x_363, x_289);
x_365 = l_Lean_Elab_Command_mkUnexpander___closed__43;
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_19);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_302);
lean_inc(x_291);
x_368 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_368, 0, x_291);
lean_ctor_set(x_368, 1, x_362);
lean_ctor_set(x_368, 2, x_364);
lean_ctor_set(x_368, 3, x_367);
lean_inc_ref(x_355);
lean_inc(x_291);
x_369 = l_Lean_Syntax_node3(x_291, x_351, x_353, x_2, x_355);
lean_inc(x_291);
x_370 = l_Lean_Syntax_node2(x_291, x_296, x_303, x_369);
lean_inc(x_291);
x_371 = l_Lean_Syntax_node2(x_291, x_361, x_368, x_370);
lean_inc_ref(x_360);
lean_inc_ref(x_350);
lean_inc(x_291);
x_372 = l_Lean_Syntax_node4(x_291, x_348, x_350, x_358, x_360, x_371);
x_373 = l_Lean_Elab_Command_mkUnexpander___closed__45;
x_374 = l_Lean_Elab_Command_mkUnexpander___closed__46;
lean_inc(x_291);
x_375 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_375, 0, x_291);
lean_ctor_set(x_375, 1, x_374);
lean_inc(x_291);
x_376 = l_Lean_Syntax_node1(x_291, x_373, x_375);
lean_inc(x_291);
x_377 = l_Lean_Syntax_node1(x_291, x_296, x_376);
lean_inc(x_291);
x_378 = l_Lean_Syntax_node1(x_291, x_296, x_377);
x_379 = l_Lean_Elab_Command_mkUnexpander___closed__48;
x_380 = l_Lean_Elab_Command_mkUnexpander___closed__49;
lean_inc(x_289);
lean_inc(x_288);
x_381 = l_Lean_addMacroScope(x_288, x_380, x_289);
x_382 = l_Lean_Elab_Command_mkUnexpander___closed__51;
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_19);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_302);
lean_inc(x_291);
x_385 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_385, 0, x_291);
lean_ctor_set(x_385, 1, x_379);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_384);
x_386 = l_Lean_Elab_Command_mkUnexpander___closed__53;
x_387 = l_Lean_Elab_Command_removeParentheses___closed__3;
x_388 = l_Lean_Elab_Command_mkUnexpander___closed__54;
lean_inc(x_291);
x_389 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_389, 0, x_291);
lean_ctor_set(x_389, 1, x_388);
x_390 = l_Lean_Elab_Command_removeParentheses___closed__5;
x_391 = l_Lean_Elab_Command_mkUnexpander___closed__56;
x_392 = lean_box(0);
x_393 = l_Lean_addMacroScope(x_288, x_392, x_289);
x_394 = l_Lean_Elab_Command_mkUnexpander___closed__68;
lean_inc(x_291);
x_395 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_395, 0, x_291);
lean_ctor_set(x_395, 1, x_391);
lean_ctor_set(x_395, 2, x_393);
lean_ctor_set(x_395, 3, x_394);
lean_inc(x_291);
x_396 = l_Lean_Syntax_node1(x_291, x_390, x_395);
lean_inc(x_291);
x_397 = l_Lean_Syntax_node2(x_291, x_387, x_389, x_396);
lean_inc_ref(x_298);
lean_inc(x_291);
x_398 = l_Lean_Syntax_node3(x_291, x_386, x_397, x_298, x_355);
lean_inc(x_291);
x_399 = l_Lean_Syntax_node1(x_291, x_296, x_398);
lean_inc(x_291);
x_400 = l_Lean_Syntax_node2(x_291, x_361, x_385, x_399);
lean_inc(x_291);
x_401 = l_Lean_Syntax_node4(x_291, x_348, x_350, x_378, x_360, x_400);
lean_inc(x_291);
x_402 = l_Lean_Syntax_node2(x_291, x_296, x_372, x_401);
lean_inc(x_291);
x_403 = l_Lean_Syntax_node1(x_291, x_347, x_402);
lean_inc(x_291);
x_404 = l_Lean_Syntax_node2(x_291, x_345, x_346, x_403);
x_405 = l_Lean_Syntax_node8(x_291, x_312, x_298, x_330, x_331, x_336, x_306, x_341, x_343, x_404);
x_406 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_406, 0, x_405);
if (lean_is_scalar(x_286)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_286;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_285);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; 
lean_dec(x_284);
lean_dec(x_280);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_408 = lean_box(0);
if (lean_is_scalar(x_286)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_286;
}
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_285);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_280);
lean_free_object(x_16);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_410 = lean_ctor_get(x_283, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_283, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_412 = x_283;
} else {
 lean_dec_ref(x_283);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
}
else
{
lean_object* x_414; 
lean_free_object(x_16);
lean_dec_ref(x_21);
lean_dec(x_18);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_414 = lean_ctor_get(x_15, 1);
lean_inc(x_414);
lean_dec_ref(x_15);
x_6 = x_414;
goto block_9;
}
}
else
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_16, 1);
lean_inc(x_415);
lean_dec(x_16);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; size_t x_419; size_t x_420; lean_object* x_421; 
x_416 = lean_ctor_get(x_15, 1);
lean_inc(x_416);
lean_dec_ref(x_15);
x_417 = lean_ctor_get(x_18, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_418 = x_18;
} else {
 lean_dec_ref(x_18);
 x_418 = lean_box(0);
}
x_419 = lean_array_size(x_11);
x_420 = 0;
lean_inc_ref(x_12);
x_421 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_removeParentheses_spec__0(x_419, x_420, x_11, x_12, x_416);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_424 = x_421;
} else {
 lean_dec_ref(x_421);
 x_424 = lean_box(0);
}
x_425 = l_Lean_Elab_Command_hasDuplicateAntiquot(x_422);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_426 = lean_ctor_get(x_12, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_12, 2);
lean_inc(x_427);
x_428 = lean_ctor_get(x_12, 5);
lean_inc(x_428);
lean_dec_ref(x_12);
x_429 = l_Lean_SourceInfo_fromRef(x_428, x_425);
lean_dec(x_428);
x_430 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0;
x_431 = l_Lean_Elab_Command_mkUnexpander___closed__1;
x_432 = l_Lean_Elab_Command_mkUnexpander___closed__2;
lean_inc(x_429);
if (lean_is_scalar(x_418)) {
 x_433 = lean_alloc_ctor(2, 2, 0);
} else {
 x_433 = x_418;
 lean_ctor_set_tag(x_433, 2);
}
lean_ctor_set(x_433, 0, x_429);
lean_ctor_set(x_433, 1, x_432);
x_434 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_435 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7;
lean_inc(x_429);
x_436 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_436, 0, x_429);
lean_ctor_set(x_436, 1, x_434);
lean_ctor_set(x_436, 2, x_435);
x_437 = l_Lean_Elab_Command_mkUnexpander___closed__4;
x_438 = l_Lean_Elab_Command_mkUnexpander___closed__5;
lean_inc(x_427);
lean_inc(x_426);
x_439 = l_Lean_addMacroScope(x_426, x_438, x_427);
x_440 = lean_box(0);
lean_inc(x_429);
x_441 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_441, 0, x_429);
lean_ctor_set(x_441, 1, x_437);
lean_ctor_set(x_441, 2, x_439);
lean_ctor_set(x_441, 3, x_440);
x_442 = l_Lean_Elab_Command_mkUnexpander___closed__7;
x_443 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
lean_inc(x_429);
x_444 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_444, 0, x_429);
lean_ctor_set(x_444, 1, x_443);
lean_inc(x_429);
x_445 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_445, 0, x_429);
lean_ctor_set(x_445, 1, x_430);
lean_inc_ref(x_444);
lean_inc(x_429);
x_446 = l_Lean_Syntax_node2(x_429, x_442, x_444, x_445);
lean_inc_ref(x_441);
lean_inc_ref(x_436);
lean_inc(x_429);
x_447 = l_Lean_Syntax_node4(x_429, x_431, x_433, x_436, x_441, x_446);
x_448 = l_Lean_Syntax_mkApp(x_447, x_422);
x_449 = l_Lean_Elab_Command_mkUnexpander___closed__9;
x_450 = l_Lean_Elab_Command_mkUnexpander___closed__10;
x_451 = l_Lean_Elab_Command_mkUnexpander___closed__12;
x_452 = l_Lean_Elab_Command_mkUnexpander___closed__13;
lean_inc(x_429);
x_453 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_453, 0, x_429);
lean_ctor_set(x_453, 1, x_452);
x_454 = l_Lean_Elab_Command_addInheritDocDefault___closed__6;
x_455 = l_Lean_Elab_Command_mkUnexpander___closed__14;
x_456 = l_Lean_Elab_Command_mkUnexpander___closed__16;
x_457 = l_Lean_Elab_Command_mkUnexpander___closed__17;
lean_inc(x_427);
lean_inc(x_426);
x_458 = l_Lean_addMacroScope(x_426, x_457, x_427);
lean_inc(x_429);
x_459 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_459, 0, x_429);
lean_ctor_set(x_459, 1, x_456);
lean_ctor_set(x_459, 2, x_458);
lean_ctor_set(x_459, 3, x_440);
x_460 = lean_mk_syntax_ident(x_417);
lean_inc(x_460);
lean_inc(x_429);
x_461 = l_Lean_Syntax_node1(x_429, x_434, x_460);
lean_inc(x_429);
x_462 = l_Lean_Syntax_node2(x_429, x_455, x_459, x_461);
lean_inc(x_429);
x_463 = l_Lean_Syntax_node2(x_429, x_454, x_1, x_462);
lean_inc(x_429);
x_464 = l_Lean_Syntax_node1(x_429, x_434, x_463);
x_465 = l_Lean_Elab_Command_mkUnexpander___closed__18;
lean_inc(x_429);
x_466 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_466, 0, x_429);
lean_ctor_set(x_466, 1, x_465);
lean_inc(x_429);
x_467 = l_Lean_Syntax_node3(x_429, x_451, x_453, x_464, x_466);
lean_inc(x_429);
x_468 = l_Lean_Syntax_node1(x_429, x_434, x_467);
lean_inc(x_429);
x_469 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_469, 0, x_429);
lean_ctor_set(x_469, 1, x_449);
x_470 = l_Lean_Elab_Command_mkUnexpander___closed__20;
x_471 = l_Lean_Elab_Command_mkUnexpander___closed__21;
lean_inc(x_427);
lean_inc(x_426);
x_472 = l_Lean_addMacroScope(x_426, x_471, x_427);
lean_inc(x_429);
x_473 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_473, 0, x_429);
lean_ctor_set(x_473, 1, x_470);
lean_ctor_set(x_473, 2, x_472);
lean_ctor_set(x_473, 3, x_440);
lean_inc(x_429);
x_474 = l_Lean_Syntax_node2(x_429, x_434, x_473, x_460);
x_475 = l_Lean_Elab_Command_mkUnexpander___closed__23;
x_476 = l_Lean_Elab_Command_mkUnexpander___closed__26;
lean_inc(x_427);
lean_inc(x_426);
x_477 = l_Lean_addMacroScope(x_426, x_476, x_427);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_19);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_440);
lean_inc(x_429);
x_480 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_480, 0, x_429);
lean_ctor_set(x_480, 1, x_475);
lean_ctor_set(x_480, 2, x_477);
lean_ctor_set(x_480, 3, x_479);
x_481 = l_Lean_Elab_Command_mkUnexpander___closed__27;
lean_inc(x_429);
x_482 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_482, 0, x_429);
lean_ctor_set(x_482, 1, x_481);
x_483 = l_Lean_Elab_Command_mkUnexpander___closed__28;
x_484 = l_Lean_Elab_Command_mkUnexpander___closed__29;
lean_inc(x_429);
x_485 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_485, 0, x_429);
lean_ctor_set(x_485, 1, x_483);
x_486 = l_Lean_Elab_Command_mkUnexpander___closed__31;
x_487 = l_Lean_Elab_Command_mkUnexpander___closed__33;
x_488 = l_Lean_Elab_Command_mkUnexpander___closed__34;
lean_inc(x_429);
x_489 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_489, 0, x_429);
lean_ctor_set(x_489, 1, x_488);
x_490 = l_Lean_Elab_Command_mkUnexpander___closed__36;
x_491 = l_Lean_Elab_Command_mkUnexpander___closed__37;
lean_inc(x_429);
x_492 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_492, 0, x_429);
lean_ctor_set(x_492, 1, x_491);
x_493 = l_Lean_Elab_Command_mkUnexpander___closed__38;
lean_inc(x_429);
x_494 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_494, 0, x_429);
lean_ctor_set(x_494, 1, x_493);
lean_inc_ref(x_494);
lean_inc_ref(x_492);
lean_inc(x_429);
x_495 = l_Lean_Syntax_node3(x_429, x_490, x_492, x_448, x_494);
lean_inc(x_429);
x_496 = l_Lean_Syntax_node1(x_429, x_434, x_495);
lean_inc(x_429);
x_497 = l_Lean_Syntax_node1(x_429, x_434, x_496);
x_498 = l_Lean_Elab_Command_mkUnexpander___closed__39;
lean_inc(x_429);
x_499 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_499, 0, x_429);
lean_ctor_set(x_499, 1, x_498);
x_500 = l_Lean_Elab_Command_addInheritDocDefault___closed__4;
x_501 = l_Lean_Elab_Command_mkUnexpander___closed__41;
x_502 = l_Lean_Elab_Command_mkUnexpander___closed__42;
lean_inc(x_427);
lean_inc(x_426);
x_503 = l_Lean_addMacroScope(x_426, x_502, x_427);
x_504 = l_Lean_Elab_Command_mkUnexpander___closed__43;
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_504);
lean_ctor_set(x_505, 1, x_19);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_440);
lean_inc(x_429);
x_507 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_507, 0, x_429);
lean_ctor_set(x_507, 1, x_501);
lean_ctor_set(x_507, 2, x_503);
lean_ctor_set(x_507, 3, x_506);
lean_inc_ref(x_494);
lean_inc(x_429);
x_508 = l_Lean_Syntax_node3(x_429, x_490, x_492, x_2, x_494);
lean_inc(x_429);
x_509 = l_Lean_Syntax_node2(x_429, x_434, x_441, x_508);
lean_inc(x_429);
x_510 = l_Lean_Syntax_node2(x_429, x_500, x_507, x_509);
lean_inc_ref(x_499);
lean_inc_ref(x_489);
lean_inc(x_429);
x_511 = l_Lean_Syntax_node4(x_429, x_487, x_489, x_497, x_499, x_510);
x_512 = l_Lean_Elab_Command_mkUnexpander___closed__45;
x_513 = l_Lean_Elab_Command_mkUnexpander___closed__46;
lean_inc(x_429);
x_514 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_514, 0, x_429);
lean_ctor_set(x_514, 1, x_513);
lean_inc(x_429);
x_515 = l_Lean_Syntax_node1(x_429, x_512, x_514);
lean_inc(x_429);
x_516 = l_Lean_Syntax_node1(x_429, x_434, x_515);
lean_inc(x_429);
x_517 = l_Lean_Syntax_node1(x_429, x_434, x_516);
x_518 = l_Lean_Elab_Command_mkUnexpander___closed__48;
x_519 = l_Lean_Elab_Command_mkUnexpander___closed__49;
lean_inc(x_427);
lean_inc(x_426);
x_520 = l_Lean_addMacroScope(x_426, x_519, x_427);
x_521 = l_Lean_Elab_Command_mkUnexpander___closed__51;
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_19);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_440);
lean_inc(x_429);
x_524 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_524, 0, x_429);
lean_ctor_set(x_524, 1, x_518);
lean_ctor_set(x_524, 2, x_520);
lean_ctor_set(x_524, 3, x_523);
x_525 = l_Lean_Elab_Command_mkUnexpander___closed__53;
x_526 = l_Lean_Elab_Command_removeParentheses___closed__3;
x_527 = l_Lean_Elab_Command_mkUnexpander___closed__54;
lean_inc(x_429);
x_528 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_528, 0, x_429);
lean_ctor_set(x_528, 1, x_527);
x_529 = l_Lean_Elab_Command_removeParentheses___closed__5;
x_530 = l_Lean_Elab_Command_mkUnexpander___closed__56;
x_531 = lean_box(0);
x_532 = l_Lean_addMacroScope(x_426, x_531, x_427);
x_533 = l_Lean_Elab_Command_mkUnexpander___closed__68;
lean_inc(x_429);
x_534 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_534, 0, x_429);
lean_ctor_set(x_534, 1, x_530);
lean_ctor_set(x_534, 2, x_532);
lean_ctor_set(x_534, 3, x_533);
lean_inc(x_429);
x_535 = l_Lean_Syntax_node1(x_429, x_529, x_534);
lean_inc(x_429);
x_536 = l_Lean_Syntax_node2(x_429, x_526, x_528, x_535);
lean_inc_ref(x_436);
lean_inc(x_429);
x_537 = l_Lean_Syntax_node3(x_429, x_525, x_536, x_436, x_494);
lean_inc(x_429);
x_538 = l_Lean_Syntax_node1(x_429, x_434, x_537);
lean_inc(x_429);
x_539 = l_Lean_Syntax_node2(x_429, x_500, x_524, x_538);
lean_inc(x_429);
x_540 = l_Lean_Syntax_node4(x_429, x_487, x_489, x_517, x_499, x_539);
lean_inc(x_429);
x_541 = l_Lean_Syntax_node2(x_429, x_434, x_511, x_540);
lean_inc(x_429);
x_542 = l_Lean_Syntax_node1(x_429, x_486, x_541);
lean_inc(x_429);
x_543 = l_Lean_Syntax_node2(x_429, x_484, x_485, x_542);
x_544 = l_Lean_Syntax_node8(x_429, x_450, x_436, x_468, x_469, x_474, x_444, x_480, x_482, x_543);
x_545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_545, 0, x_544);
if (lean_is_scalar(x_424)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_424;
}
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_423);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; 
lean_dec(x_422);
lean_dec(x_418);
lean_dec(x_417);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_547 = lean_box(0);
if (lean_is_scalar(x_424)) {
 x_548 = lean_alloc_ctor(0, 2, 0);
} else {
 x_548 = x_424;
}
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_423);
return x_548;
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_418);
lean_dec(x_417);
lean_dec_ref(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_549 = lean_ctor_get(x_421, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_421, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_551 = x_421;
} else {
 lean_dec_ref(x_421);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_550);
return x_552;
}
}
else
{
lean_object* x_553; 
lean_dec_ref(x_415);
lean_dec(x_18);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_553 = lean_ctor_get(x_15, 1);
lean_inc(x_553);
lean_dec_ref(x_15);
x_6 = x_553;
goto block_9;
}
}
}
else
{
lean_object* x_554; 
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_554 = lean_ctor_get(x_15, 1);
lean_inc(x_554);
lean_dec_ref(x_15);
x_6 = x_554;
goto block_9;
}
}
}
else
{
uint8_t x_555; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_555 = !lean_is_exclusive(x_15);
if (x_555 == 0)
{
return x_15;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_15, 0);
x_557 = lean_ctor_get(x_15, 1);
lean_inc(x_557);
lean_inc(x_556);
lean_dec(x_15);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_557);
return x_558;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
lean_inc_ref(x_4);
x_9 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_13, x_2, x_10);
x_2 = x_15;
x_3 = x_16;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_12, x_2, x_9);
x_2 = x_14;
x_3 = x_15;
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Syntax_getArg(x_6, x_1);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
x_12 = l_Lean_Syntax_getKind(x_11);
x_13 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10;
x_14 = lean_name_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addMacroScopeIfLocal___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_12; 
x_12 = l_Lean_Elab_Command_isLocalAttrKind(x_2);
if (x_12 == 0)
{
x_5 = x_12;
goto block_11;
}
else
{
uint8_t x_13; 
x_13 = l_Lean_Name_hasMacroScopes(x_1);
if (x_13 == 0)
{
x_5 = x_12;
goto block_11;
}
else
{
lean_object* x_14; 
lean_dec_ref(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
block_11:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = l_Lean_addMacroScope(x_7, x_1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = l_Lean_SourceInfo_fromRef(x_1, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("namedPrio", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("priority", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("macro_rules", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckedQuot", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("section", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sectionHeader", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("set_option", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quotPrecheck.allowSectionVars", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__12;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quotPrecheck", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("allowSectionVars", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__15;
x_2 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("end", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("namedName", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("syntax", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__21;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_56; 
lean_inc_ref(x_11);
x_56 = l_Lean_evalOptPrio(x_8, x_11, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_array_size(x_9);
x_60 = 0;
lean_inc_ref(x_11);
lean_inc_ref(x_9);
x_61 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0(x_59, x_60, x_9, x_11, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3;
x_65 = 0;
x_66 = l_Lean_mkIdentFrom(x_1, x_64, x_65);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_429 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_430 = lean_box(2);
lean_inc(x_62);
x_431 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_429);
lean_ctor_set(x_431, 2, x_62);
lean_inc_ref(x_11);
x_432 = l_Lean_Elab_Command_mkNameFromParserSyntax(x_64, x_431, x_11, x_63);
lean_dec_ref(x_431);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec_ref(x_432);
lean_inc_ref(x_11);
lean_inc(x_5);
x_435 = l_Lean_Elab_Command_addMacroScopeIfLocal___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__5(x_433, x_5, x_11, x_434);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec_ref(x_435);
x_418 = x_436;
x_419 = x_11;
x_420 = x_437;
goto block_428;
}
else
{
uint8_t x_438; 
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_57);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_438 = !lean_is_exclusive(x_432);
if (x_438 == 0)
{
return x_432;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_432, 0);
x_440 = lean_ctor_get(x_432, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_432);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
else
{
lean_object* x_442; lean_object* x_443; 
x_442 = lean_ctor_get(x_7, 0);
lean_inc(x_442);
x_443 = l_Lean_Syntax_getId(x_442);
lean_dec(x_442);
x_418 = x_443;
x_419 = x_11;
x_420 = x_63;
goto block_428;
}
block_282:
{
lean_object* x_91; uint8_t x_92; 
x_91 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(x_67, x_84, x_82);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
x_95 = l_Lean_Elab_Command_mkUnexpander___closed__38;
lean_inc(x_81);
lean_ctor_set_tag(x_91, 2);
lean_ctor_set(x_91, 1, x_95);
lean_ctor_set(x_91, 0, x_81);
lean_inc_ref(x_91);
lean_inc(x_77);
lean_inc(x_89);
lean_inc(x_81);
x_96 = l_Lean_Syntax_node5(x_81, x_72, x_89, x_69, x_77, x_90, x_91);
lean_inc(x_75);
lean_inc(x_81);
x_97 = l_Lean_Syntax_node1(x_81, x_75, x_96);
x_98 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__2;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_99 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_98);
x_100 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__3;
lean_inc(x_81);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_81);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Nat_reprFast(x_57);
lean_inc(x_73);
x_103 = l_Lean_Syntax_mkNumLit(x_102, x_73);
lean_inc(x_81);
x_104 = l_Lean_Syntax_node5(x_81, x_99, x_89, x_101, x_77, x_103, x_91);
lean_inc(x_75);
lean_inc(x_81);
x_105 = l_Lean_Syntax_node1(x_81, x_75, x_104);
x_106 = lean_array_size(x_62);
x_107 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3(x_106, x_60, x_62);
lean_inc_ref(x_68);
x_108 = l_Array_append___redArg(x_68, x_107);
lean_dec_ref(x_107);
lean_inc(x_75);
lean_inc(x_81);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_81);
lean_ctor_set(x_109, 1, x_75);
lean_ctor_set(x_109, 2, x_108);
x_110 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
lean_inc(x_81);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_81);
lean_ctor_set(x_111, 1, x_110);
x_112 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__4;
x_113 = lean_array_push(x_112, x_85);
x_114 = lean_array_push(x_113, x_80);
lean_inc(x_5);
x_115 = lean_array_push(x_114, x_5);
x_116 = lean_array_push(x_115, x_88);
x_117 = lean_array_push(x_116, x_74);
x_118 = lean_array_push(x_117, x_97);
x_119 = lean_array_push(x_118, x_105);
x_120 = lean_array_push(x_119, x_109);
x_121 = lean_array_push(x_120, x_111);
x_122 = lean_array_push(x_121, x_66);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_81);
lean_ctor_set(x_123, 1, x_70);
lean_ctor_set(x_123, 2, x_122);
x_124 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__5;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_125 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_124);
lean_inc_ref(x_68);
lean_inc(x_75);
lean_inc(x_93);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_93);
lean_ctor_set(x_126, 1, x_75);
lean_ctor_set(x_126, 2, x_68);
x_127 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_128 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_129 = l_Lean_Name_mkStr4(x_87, x_79, x_127, x_128);
lean_inc_ref(x_126);
lean_inc(x_93);
x_130 = l_Lean_Syntax_node1(x_93, x_129, x_126);
lean_inc(x_93);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_93);
lean_ctor_set(x_131, 1, x_124);
x_132 = l_Lean_Elab_Command_mkUnexpander___closed__30;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_133 = l_Lean_Name_mkStr4(x_87, x_79, x_127, x_132);
x_134 = l_Lean_Elab_Command_mkUnexpander___closed__32;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_135 = l_Lean_Name_mkStr4(x_87, x_79, x_127, x_134);
x_136 = l_Lean_Elab_Command_mkUnexpander___closed__34;
lean_inc(x_93);
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_93);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Elab_Command_mkUnexpander___closed__35;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_139 = l_Lean_Name_mkStr4(x_87, x_79, x_127, x_138);
x_140 = l_Lean_Elab_Command_mkUnexpander___closed__37;
lean_inc(x_93);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_93);
lean_ctor_set(x_141, 1, x_140);
lean_inc(x_93);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_93);
lean_ctor_set(x_142, 1, x_95);
lean_inc_ref(x_142);
lean_inc(x_83);
lean_inc_ref(x_141);
lean_inc(x_139);
lean_inc(x_93);
x_143 = l_Lean_Syntax_node3(x_93, x_139, x_141, x_83, x_142);
lean_inc(x_75);
lean_inc(x_93);
x_144 = l_Lean_Syntax_node1(x_93, x_75, x_143);
lean_inc(x_75);
lean_inc(x_93);
x_145 = l_Lean_Syntax_node1(x_93, x_75, x_144);
x_146 = l_Lean_Elab_Command_mkUnexpander___closed__39;
lean_inc(x_93);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_93);
lean_ctor_set(x_147, 1, x_146);
x_148 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__6;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_149 = l_Lean_Name_mkStr4(x_87, x_79, x_127, x_148);
x_150 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__7;
lean_inc(x_93);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_93);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_86);
lean_inc(x_93);
x_152 = l_Lean_Syntax_node3(x_93, x_139, x_141, x_86, x_142);
lean_inc(x_93);
x_153 = l_Lean_Syntax_node2(x_93, x_149, x_151, x_152);
lean_inc(x_93);
x_154 = l_Lean_Syntax_node4(x_93, x_135, x_137, x_145, x_147, x_153);
lean_inc(x_75);
lean_inc(x_93);
x_155 = l_Lean_Syntax_node1(x_93, x_75, x_154);
lean_inc(x_93);
x_156 = l_Lean_Syntax_node1(x_93, x_133, x_155);
lean_inc_ref_n(x_126, 2);
x_157 = l_Lean_Syntax_node6(x_93, x_125, x_126, x_126, x_130, x_131, x_126, x_156);
lean_inc(x_5);
x_158 = l_Lean_Elab_Command_isLocalAttrKind(x_5);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_87);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_76);
lean_dec_ref(x_71);
lean_dec_ref(x_68);
lean_dec(x_67);
x_159 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__8;
x_160 = lean_array_push(x_159, x_157);
lean_inc(x_75);
lean_inc(x_73);
x_161 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_161, 0, x_73);
lean_ctor_set(x_161, 1, x_75);
lean_ctor_set(x_161, 2, x_160);
x_13 = x_123;
x_14 = x_83;
x_15 = x_86;
x_16 = x_73;
x_17 = x_75;
x_18 = x_161;
x_19 = x_84;
x_20 = x_94;
goto block_55;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_162 = l_Lean_SourceInfo_fromRef(x_67, x_65);
lean_dec(x_67);
x_163 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__9;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_164 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_163);
x_165 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__10;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_166 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_165);
lean_inc(x_75);
lean_inc(x_162);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_162);
lean_ctor_set(x_167, 1, x_75);
lean_ctor_set(x_167, 2, x_68);
lean_inc_ref_n(x_167, 3);
lean_inc(x_162);
x_168 = l_Lean_Syntax_node3(x_162, x_166, x_167, x_167, x_167);
lean_inc(x_162);
x_169 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_169, 0, x_162);
lean_ctor_set(x_169, 1, x_163);
lean_inc_ref(x_167);
lean_inc(x_162);
x_170 = l_Lean_Syntax_node3(x_162, x_164, x_168, x_169, x_167);
x_171 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__11;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_172 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_171);
lean_inc(x_162);
x_173 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_173, 0, x_162);
lean_ctor_set(x_173, 1, x_171);
x_174 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__13;
x_175 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__16;
x_176 = l_Lean_addMacroScope(x_76, x_175, x_78);
x_177 = lean_box(0);
lean_inc(x_162);
x_178 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_178, 0, x_162);
lean_ctor_set(x_178, 1, x_174);
lean_ctor_set(x_178, 2, x_176);
lean_ctor_set(x_178, 3, x_177);
x_179 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__17;
lean_inc(x_162);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_162);
lean_ctor_set(x_180, 1, x_179);
lean_inc_ref(x_167);
lean_inc(x_162);
x_181 = l_Lean_Syntax_node4(x_162, x_172, x_173, x_178, x_167, x_180);
x_182 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__18;
x_183 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_182);
lean_inc(x_162);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_162);
lean_ctor_set(x_184, 1, x_182);
lean_inc(x_162);
x_185 = l_Lean_Syntax_node2(x_162, x_183, x_184, x_167);
lean_inc(x_75);
x_186 = l_Lean_Syntax_node4(x_162, x_75, x_170, x_181, x_157, x_185);
x_13 = x_123;
x_14 = x_83;
x_15 = x_86;
x_16 = x_73;
x_17 = x_75;
x_18 = x_186;
x_19 = x_84;
x_20 = x_94;
goto block_55;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; size_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_187 = lean_ctor_get(x_91, 0);
x_188 = lean_ctor_get(x_91, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_91);
x_189 = l_Lean_Elab_Command_mkUnexpander___closed__38;
lean_inc(x_81);
x_190 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_190, 0, x_81);
lean_ctor_set(x_190, 1, x_189);
lean_inc_ref(x_190);
lean_inc(x_77);
lean_inc(x_89);
lean_inc(x_81);
x_191 = l_Lean_Syntax_node5(x_81, x_72, x_89, x_69, x_77, x_90, x_190);
lean_inc(x_75);
lean_inc(x_81);
x_192 = l_Lean_Syntax_node1(x_81, x_75, x_191);
x_193 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__2;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_194 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_193);
x_195 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__3;
lean_inc(x_81);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_81);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Nat_reprFast(x_57);
lean_inc(x_73);
x_198 = l_Lean_Syntax_mkNumLit(x_197, x_73);
lean_inc(x_81);
x_199 = l_Lean_Syntax_node5(x_81, x_194, x_89, x_196, x_77, x_198, x_190);
lean_inc(x_75);
lean_inc(x_81);
x_200 = l_Lean_Syntax_node1(x_81, x_75, x_199);
x_201 = lean_array_size(x_62);
x_202 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3(x_201, x_60, x_62);
lean_inc_ref(x_68);
x_203 = l_Array_append___redArg(x_68, x_202);
lean_dec_ref(x_202);
lean_inc(x_75);
lean_inc(x_81);
x_204 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_204, 0, x_81);
lean_ctor_set(x_204, 1, x_75);
lean_ctor_set(x_204, 2, x_203);
x_205 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
lean_inc(x_81);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_81);
lean_ctor_set(x_206, 1, x_205);
x_207 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__4;
x_208 = lean_array_push(x_207, x_85);
x_209 = lean_array_push(x_208, x_80);
lean_inc(x_5);
x_210 = lean_array_push(x_209, x_5);
x_211 = lean_array_push(x_210, x_88);
x_212 = lean_array_push(x_211, x_74);
x_213 = lean_array_push(x_212, x_192);
x_214 = lean_array_push(x_213, x_200);
x_215 = lean_array_push(x_214, x_204);
x_216 = lean_array_push(x_215, x_206);
x_217 = lean_array_push(x_216, x_66);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_81);
lean_ctor_set(x_218, 1, x_70);
lean_ctor_set(x_218, 2, x_217);
x_219 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__5;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_220 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_219);
lean_inc_ref(x_68);
lean_inc(x_75);
lean_inc(x_187);
x_221 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_221, 0, x_187);
lean_ctor_set(x_221, 1, x_75);
lean_ctor_set(x_221, 2, x_68);
x_222 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_223 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_224 = l_Lean_Name_mkStr4(x_87, x_79, x_222, x_223);
lean_inc_ref(x_221);
lean_inc(x_187);
x_225 = l_Lean_Syntax_node1(x_187, x_224, x_221);
lean_inc(x_187);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_187);
lean_ctor_set(x_226, 1, x_219);
x_227 = l_Lean_Elab_Command_mkUnexpander___closed__30;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_228 = l_Lean_Name_mkStr4(x_87, x_79, x_222, x_227);
x_229 = l_Lean_Elab_Command_mkUnexpander___closed__32;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_230 = l_Lean_Name_mkStr4(x_87, x_79, x_222, x_229);
x_231 = l_Lean_Elab_Command_mkUnexpander___closed__34;
lean_inc(x_187);
x_232 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_232, 0, x_187);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_Elab_Command_mkUnexpander___closed__35;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_234 = l_Lean_Name_mkStr4(x_87, x_79, x_222, x_233);
x_235 = l_Lean_Elab_Command_mkUnexpander___closed__37;
lean_inc(x_187);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_187);
lean_ctor_set(x_236, 1, x_235);
lean_inc(x_187);
x_237 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_237, 0, x_187);
lean_ctor_set(x_237, 1, x_189);
lean_inc_ref(x_237);
lean_inc(x_83);
lean_inc_ref(x_236);
lean_inc(x_234);
lean_inc(x_187);
x_238 = l_Lean_Syntax_node3(x_187, x_234, x_236, x_83, x_237);
lean_inc(x_75);
lean_inc(x_187);
x_239 = l_Lean_Syntax_node1(x_187, x_75, x_238);
lean_inc(x_75);
lean_inc(x_187);
x_240 = l_Lean_Syntax_node1(x_187, x_75, x_239);
x_241 = l_Lean_Elab_Command_mkUnexpander___closed__39;
lean_inc(x_187);
x_242 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_242, 0, x_187);
lean_ctor_set(x_242, 1, x_241);
x_243 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__6;
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_244 = l_Lean_Name_mkStr4(x_87, x_79, x_222, x_243);
x_245 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__7;
lean_inc(x_187);
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_187);
lean_ctor_set(x_246, 1, x_245);
lean_inc(x_86);
lean_inc(x_187);
x_247 = l_Lean_Syntax_node3(x_187, x_234, x_236, x_86, x_237);
lean_inc(x_187);
x_248 = l_Lean_Syntax_node2(x_187, x_244, x_246, x_247);
lean_inc(x_187);
x_249 = l_Lean_Syntax_node4(x_187, x_230, x_232, x_240, x_242, x_248);
lean_inc(x_75);
lean_inc(x_187);
x_250 = l_Lean_Syntax_node1(x_187, x_75, x_249);
lean_inc(x_187);
x_251 = l_Lean_Syntax_node1(x_187, x_228, x_250);
lean_inc_ref_n(x_221, 2);
x_252 = l_Lean_Syntax_node6(x_187, x_220, x_221, x_221, x_225, x_226, x_221, x_251);
lean_inc(x_5);
x_253 = l_Lean_Elab_Command_isLocalAttrKind(x_5);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec_ref(x_87);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_76);
lean_dec_ref(x_71);
lean_dec_ref(x_68);
lean_dec(x_67);
x_254 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__8;
x_255 = lean_array_push(x_254, x_252);
lean_inc(x_75);
lean_inc(x_73);
x_256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_256, 0, x_73);
lean_ctor_set(x_256, 1, x_75);
lean_ctor_set(x_256, 2, x_255);
x_13 = x_218;
x_14 = x_83;
x_15 = x_86;
x_16 = x_73;
x_17 = x_75;
x_18 = x_256;
x_19 = x_84;
x_20 = x_188;
goto block_55;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_257 = l_Lean_SourceInfo_fromRef(x_67, x_65);
lean_dec(x_67);
x_258 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__9;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_259 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_258);
x_260 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__10;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_261 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_260);
lean_inc(x_75);
lean_inc(x_257);
x_262 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_262, 0, x_257);
lean_ctor_set(x_262, 1, x_75);
lean_ctor_set(x_262, 2, x_68);
lean_inc_ref_n(x_262, 3);
lean_inc(x_257);
x_263 = l_Lean_Syntax_node3(x_257, x_261, x_262, x_262, x_262);
lean_inc(x_257);
x_264 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_264, 0, x_257);
lean_ctor_set(x_264, 1, x_258);
lean_inc_ref(x_262);
lean_inc(x_257);
x_265 = l_Lean_Syntax_node3(x_257, x_259, x_263, x_264, x_262);
x_266 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__11;
lean_inc_ref(x_71);
lean_inc_ref(x_79);
lean_inc_ref(x_87);
x_267 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_266);
lean_inc(x_257);
x_268 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_268, 0, x_257);
lean_ctor_set(x_268, 1, x_266);
x_269 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__13;
x_270 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__16;
x_271 = l_Lean_addMacroScope(x_76, x_270, x_78);
x_272 = lean_box(0);
lean_inc(x_257);
x_273 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_273, 0, x_257);
lean_ctor_set(x_273, 1, x_269);
lean_ctor_set(x_273, 2, x_271);
lean_ctor_set(x_273, 3, x_272);
x_274 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__17;
lean_inc(x_257);
x_275 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_275, 0, x_257);
lean_ctor_set(x_275, 1, x_274);
lean_inc_ref(x_262);
lean_inc(x_257);
x_276 = l_Lean_Syntax_node4(x_257, x_267, x_268, x_273, x_262, x_275);
x_277 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__18;
x_278 = l_Lean_Name_mkStr4(x_87, x_79, x_71, x_277);
lean_inc(x_257);
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_257);
lean_ctor_set(x_279, 1, x_277);
lean_inc(x_257);
x_280 = l_Lean_Syntax_node2(x_257, x_278, x_279, x_262);
lean_inc(x_75);
x_281 = l_Lean_Syntax_node4(x_257, x_75, x_265, x_276, x_252, x_280);
x_13 = x_218;
x_14 = x_83;
x_15 = x_86;
x_16 = x_73;
x_17 = x_75;
x_18 = x_281;
x_19 = x_84;
x_20 = x_188;
goto block_55;
}
}
}
block_315:
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_inc_ref(x_284);
x_303 = l_Array_append___redArg(x_284, x_302);
lean_dec_ref(x_302);
lean_inc(x_289);
lean_inc(x_294);
x_304 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_304, 0, x_294);
lean_ctor_set(x_304, 1, x_289);
lean_ctor_set(x_304, 2, x_303);
x_305 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__19;
lean_inc_ref(x_286);
lean_inc_ref(x_291);
lean_inc_ref(x_300);
x_306 = l_Lean_Name_mkStr4(x_300, x_291, x_286, x_305);
x_307 = l_Lean_Elab_Command_mkUnexpander___closed__54;
lean_inc(x_294);
x_308 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_308, 0, x_294);
lean_ctor_set(x_308, 1, x_307);
x_309 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__20;
lean_inc(x_294);
x_310 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_310, 0, x_294);
lean_ctor_set(x_310, 1, x_309);
x_311 = l_Lean_Elab_Command_mkUnexpander___closed__27;
lean_inc(x_294);
x_312 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_312, 0, x_294);
lean_ctor_set(x_312, 1, x_311);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_313; 
x_313 = lean_mk_syntax_ident(x_287);
x_67 = x_283;
x_68 = x_284;
x_69 = x_310;
x_70 = x_285;
x_71 = x_286;
x_72 = x_306;
x_73 = x_288;
x_74 = x_304;
x_75 = x_289;
x_76 = x_290;
x_77 = x_312;
x_78 = x_292;
x_79 = x_291;
x_80 = x_293;
x_81 = x_294;
x_82 = x_295;
x_83 = x_296;
x_84 = x_297;
x_85 = x_298;
x_86 = x_299;
x_87 = x_300;
x_88 = x_301;
x_89 = x_308;
x_90 = x_313;
goto block_282;
}
else
{
lean_object* x_314; 
lean_dec(x_287);
x_314 = lean_ctor_get(x_7, 0);
lean_inc(x_314);
lean_dec_ref(x_7);
x_67 = x_283;
x_68 = x_284;
x_69 = x_310;
x_70 = x_285;
x_71 = x_286;
x_72 = x_306;
x_73 = x_288;
x_74 = x_304;
x_75 = x_289;
x_76 = x_290;
x_77 = x_312;
x_78 = x_292;
x_79 = x_291;
x_80 = x_293;
x_81 = x_294;
x_82 = x_295;
x_83 = x_296;
x_84 = x_297;
x_85 = x_298;
x_86 = x_299;
x_87 = x_300;
x_88 = x_301;
x_89 = x_308;
x_90 = x_314;
goto block_282;
}
}
block_346:
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_inc_ref(x_317);
x_335 = l_Array_append___redArg(x_317, x_334);
lean_dec_ref(x_334);
lean_inc(x_323);
lean_inc(x_327);
x_336 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_336, 0, x_327);
lean_ctor_set(x_336, 1, x_323);
lean_ctor_set(x_336, 2, x_335);
lean_inc(x_327);
x_337 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_337, 0, x_327);
lean_ctor_set(x_337, 1, x_319);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_338; 
x_338 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4;
x_283 = x_316;
x_284 = x_317;
x_285 = x_318;
x_286 = x_320;
x_287 = x_321;
x_288 = x_322;
x_289 = x_323;
x_290 = x_324;
x_291 = x_325;
x_292 = x_326;
x_293 = x_336;
x_294 = x_327;
x_295 = x_328;
x_296 = x_329;
x_297 = x_330;
x_298 = x_331;
x_299 = x_332;
x_300 = x_333;
x_301 = x_337;
x_302 = x_338;
goto block_315;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_339 = lean_ctor_get(x_6, 0);
lean_inc(x_339);
lean_dec_ref(x_6);
x_340 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5;
lean_inc_ref(x_325);
lean_inc_ref(x_333);
x_341 = l_Lean_Name_mkStr3(x_333, x_325, x_340);
x_342 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
lean_inc(x_327);
x_343 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_343, 0, x_327);
lean_ctor_set(x_343, 1, x_342);
lean_inc(x_327);
x_344 = l_Lean_Syntax_node2(x_327, x_341, x_343, x_339);
x_345 = l_Array_mkArray1___redArg(x_344);
x_283 = x_316;
x_284 = x_317;
x_285 = x_318;
x_286 = x_320;
x_287 = x_321;
x_288 = x_322;
x_289 = x_323;
x_290 = x_324;
x_291 = x_325;
x_292 = x_326;
x_293 = x_336;
x_294 = x_327;
x_295 = x_328;
x_296 = x_329;
x_297 = x_330;
x_298 = x_331;
x_299 = x_332;
x_300 = x_333;
x_301 = x_337;
x_302 = x_345;
goto block_315;
}
}
block_381:
{
lean_object* x_366; lean_object* x_367; 
lean_inc_ref(x_348);
x_366 = l_Array_append___redArg(x_348, x_365);
lean_dec_ref(x_365);
lean_inc(x_354);
lean_inc(x_358);
x_367 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_367, 0, x_358);
lean_ctor_set(x_367, 1, x_354);
lean_ctor_set(x_367, 2, x_366);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_368; 
x_368 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4;
x_316 = x_347;
x_317 = x_348;
x_318 = x_349;
x_319 = x_350;
x_320 = x_351;
x_321 = x_352;
x_322 = x_353;
x_323 = x_354;
x_324 = x_355;
x_325 = x_356;
x_326 = x_357;
x_327 = x_358;
x_328 = x_359;
x_329 = x_360;
x_330 = x_361;
x_331 = x_367;
x_332 = x_362;
x_333 = x_363;
x_334 = x_368;
goto block_346;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_369 = lean_ctor_get(x_364, 0);
lean_inc(x_369);
lean_dec_ref(x_364);
x_370 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_371 = l_Lean_Elab_Command_mkUnexpander___closed__11;
lean_inc_ref(x_356);
lean_inc_ref(x_363);
x_372 = l_Lean_Name_mkStr4(x_363, x_356, x_370, x_371);
x_373 = l_Lean_Elab_Command_mkUnexpander___closed__13;
lean_inc(x_358);
x_374 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_374, 0, x_358);
lean_ctor_set(x_374, 1, x_373);
lean_inc_ref(x_348);
x_375 = l_Array_append___redArg(x_348, x_369);
lean_dec(x_369);
lean_inc(x_354);
lean_inc(x_358);
x_376 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_376, 0, x_358);
lean_ctor_set(x_376, 1, x_354);
lean_ctor_set(x_376, 2, x_375);
x_377 = l_Lean_Elab_Command_mkUnexpander___closed__18;
lean_inc(x_358);
x_378 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_378, 0, x_358);
lean_ctor_set(x_378, 1, x_377);
lean_inc(x_358);
x_379 = l_Lean_Syntax_node3(x_358, x_372, x_374, x_376, x_378);
x_380 = l_Array_mkArray1___redArg(x_379);
x_316 = x_347;
x_317 = x_348;
x_318 = x_349;
x_319 = x_350;
x_320 = x_351;
x_321 = x_352;
x_322 = x_353;
x_323 = x_354;
x_324 = x_355;
x_325 = x_356;
x_326 = x_357;
x_327 = x_358;
x_328 = x_359;
x_329 = x_360;
x_330 = x_361;
x_331 = x_367;
x_332 = x_362;
x_333 = x_363;
x_334 = x_380;
goto block_346;
}
}
block_417:
{
lean_object* x_387; 
x_387 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___redArg(x_59, x_60, x_9, x_384);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; size_t x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec_ref(x_387);
x_390 = lean_ctor_get(x_383, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_383, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_383, 5);
lean_inc(x_392);
x_393 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(x_392, x_383, x_389);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec_ref(x_393);
x_396 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_397 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_398 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_399 = lean_array_size(x_386);
x_400 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2(x_382, x_399, x_60, x_386);
lean_inc(x_10);
x_401 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(x_400, x_10);
lean_dec_ref(x_400);
x_402 = l_Lean_Elab_Command_addInheritDocDefault(x_10, x_4);
lean_inc(x_385);
x_403 = l_Lean_Name_append(x_2, x_385);
x_404 = lean_box(2);
x_405 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_403);
lean_ctor_set(x_405, 2, x_388);
x_406 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__21;
x_407 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__22;
x_408 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6;
x_409 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7;
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_410; 
x_410 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4;
x_347 = x_392;
x_348 = x_409;
x_349 = x_407;
x_350 = x_406;
x_351 = x_398;
x_352 = x_385;
x_353 = x_404;
x_354 = x_408;
x_355 = x_390;
x_356 = x_397;
x_357 = x_391;
x_358 = x_394;
x_359 = x_395;
x_360 = x_405;
x_361 = x_383;
x_362 = x_401;
x_363 = x_396;
x_364 = x_402;
x_365 = x_410;
goto block_381;
}
else
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_3, 0);
lean_inc(x_411);
lean_dec_ref(x_3);
x_412 = l_Array_mkArray1___redArg(x_411);
x_347 = x_392;
x_348 = x_409;
x_349 = x_407;
x_350 = x_406;
x_351 = x_398;
x_352 = x_385;
x_353 = x_404;
x_354 = x_408;
x_355 = x_390;
x_356 = x_397;
x_357 = x_391;
x_358 = x_394;
x_359 = x_395;
x_360 = x_405;
x_361 = x_383;
x_362 = x_401;
x_363 = x_396;
x_364 = x_402;
x_365 = x_412;
goto block_381;
}
}
else
{
uint8_t x_413; 
lean_dec_ref(x_386);
lean_dec(x_385);
lean_dec_ref(x_383);
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_413 = !lean_is_exclusive(x_387);
if (x_413 == 0)
{
return x_387;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_387, 0);
x_415 = lean_ctor_get(x_387, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_387);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
}
block_428:
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_421 = lean_unsigned_to_nat(0u);
x_422 = lean_array_get_size(x_9);
x_423 = l_Lean_Elab_Command_mkUnexpander___closed__69;
x_424 = lean_nat_dec_lt(x_421, x_422);
if (x_424 == 0)
{
lean_dec(x_422);
x_382 = x_421;
x_383 = x_419;
x_384 = x_420;
x_385 = x_418;
x_386 = x_423;
goto block_417;
}
else
{
uint8_t x_425; 
x_425 = lean_nat_dec_le(x_422, x_422);
if (x_425 == 0)
{
lean_dec(x_422);
x_382 = x_421;
x_383 = x_419;
x_384 = x_420;
x_385 = x_418;
x_386 = x_423;
goto block_417;
}
else
{
size_t x_426; lean_object* x_427; 
x_426 = lean_usize_of_nat(x_422);
lean_dec(x_422);
x_427 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__4(x_9, x_60, x_426, x_423);
x_382 = x_421;
x_383 = x_419;
x_384 = x_420;
x_385 = x_418;
x_386 = x_427;
goto block_417;
}
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_57);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_444 = !lean_is_exclusive(x_61);
if (x_444 == 0)
{
return x_61;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_61, 0);
x_446 = lean_ctor_get(x_61, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_61);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
else
{
uint8_t x_448; 
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_448 = !lean_is_exclusive(x_56);
if (x_448 == 0)
{
return x_56;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_56, 0);
x_450 = lean_ctor_get(x_56, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_56);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
block_55:
{
lean_object* x_21; 
x_21 = l_Lean_Elab_Command_mkUnexpander(x_5, x_14, x_15, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__0;
x_26 = lean_array_push(x_25, x_13);
x_27 = lean_array_push(x_26, x_18);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__0;
x_31 = lean_array_push(x_30, x_13);
x_32 = lean_array_push(x_31, x_18);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_21, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
lean_dec_ref(x_22);
x_38 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__1;
x_39 = lean_array_push(x_38, x_13);
x_40 = lean_array_push(x_39, x_18);
x_41 = lean_array_push(x_40, x_37);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_16);
lean_ctor_set(x_42, 1, x_17);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_21, 0, x_42);
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_dec(x_21);
x_44 = lean_ctor_get(x_22, 0);
lean_inc(x_44);
lean_dec_ref(x_22);
x_45 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__1;
x_46 = lean_array_push(x_45, x_13);
x_47 = lean_array_push(x_46, x_18);
x_48 = lean_array_push(x_47, x_44);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_16);
lean_ctor_set(x_49, 1, x_17);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_21, 0);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_21);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__0(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___redArg(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__1(x_6, x_7, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux_spec__4(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotation___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("notation", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotation___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_expandNotation___closed__0;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__2;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotation___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__19;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0;
x_2 = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotation___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("docComment", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandNotation___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_expandNotation___closed__5;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_3 = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandNotation(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Elab_Command_expandNotation___closed__1;
lean_inc(x_1);
x_33 = l_Lean_Syntax_isOfKind(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_120; uint8_t x_121; 
x_35 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_Syntax_getArg(x_1, x_35);
x_121 = l_Lean_Syntax_isNone(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_unsigned_to_nat(1u);
lean_inc(x_120);
x_123 = l_Lean_Syntax_matchesNull(x_120, x_122);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_120);
lean_dec_ref(x_2);
lean_dec(x_1);
x_124 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = l_Lean_Syntax_getArg(x_120, x_35);
lean_dec(x_120);
x_126 = l_Lean_Elab_Command_expandNotation___closed__6;
lean_inc(x_125);
x_127 = l_Lean_Syntax_isOfKind(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_125);
lean_dec_ref(x_2);
lean_dec(x_1);
x_128 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_125);
x_103 = x_129;
x_104 = x_2;
x_105 = x_3;
goto block_119;
}
}
}
else
{
lean_object* x_130; 
lean_dec(x_120);
x_130 = lean_box(0);
x_103 = x_130;
x_104 = x_2;
x_105 = x_3;
goto block_119;
}
block_57:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(6u);
x_46 = l_Lean_Syntax_getArg(x_1, x_45);
x_47 = l_Lean_Syntax_isNone(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_inc(x_46);
x_48 = l_Lean_Syntax_matchesNull(x_46, x_41);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_46);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_1);
x_49 = l_Lean_Macro_throwUnsupported___redArg(x_44);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_Syntax_getArg(x_46, x_35);
lean_dec(x_46);
x_51 = l_Lean_Elab_Command_expandNotation___closed__2;
lean_inc(x_50);
x_52 = l_Lean_Syntax_isOfKind(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_1);
x_53 = l_Lean_Macro_throwUnsupported___redArg(x_44);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_Syntax_getArg(x_50, x_37);
lean_dec(x_50);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_4 = x_42;
x_5 = x_36;
x_6 = x_38;
x_7 = x_39;
x_8 = x_40;
x_9 = x_55;
x_10 = x_43;
x_11 = x_44;
goto block_31;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_46);
x_56 = lean_box(0);
x_4 = x_42;
x_5 = x_36;
x_6 = x_38;
x_7 = x_39;
x_8 = x_40;
x_9 = x_56;
x_10 = x_43;
x_11 = x_44;
goto block_31;
}
}
block_78:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_unsigned_to_nat(5u);
x_67 = l_Lean_Syntax_getArg(x_1, x_66);
x_68 = l_Lean_Syntax_isNone(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
lean_inc(x_67);
x_69 = l_Lean_Syntax_matchesNull(x_67, x_62);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_67);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_1);
x_70 = l_Lean_Macro_throwUnsupported___redArg(x_65);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = l_Lean_Syntax_getArg(x_67, x_35);
lean_dec(x_67);
x_72 = l_Lean_Elab_Command_expandNotation___closed__3;
lean_inc(x_71);
x_73 = l_Lean_Syntax_isOfKind(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_71);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_1);
x_74 = l_Lean_Macro_throwUnsupported___redArg(x_65);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Lean_Syntax_getArg(x_71, x_59);
lean_dec(x_71);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_36 = x_58;
x_37 = x_59;
x_38 = x_60;
x_39 = x_63;
x_40 = x_61;
x_41 = x_62;
x_42 = x_76;
x_43 = x_64;
x_44 = x_65;
goto block_57;
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_67);
x_77 = lean_box(0);
x_36 = x_58;
x_37 = x_59;
x_38 = x_60;
x_39 = x_63;
x_40 = x_61;
x_41 = x_62;
x_42 = x_77;
x_43 = x_64;
x_44 = x_65;
goto block_57;
}
}
block_102:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_unsigned_to_nat(2u);
x_85 = l_Lean_Syntax_getArg(x_1, x_84);
x_86 = l_Lean_Elab_Command_expandNotation___closed__4;
lean_inc(x_85);
x_87 = l_Lean_Syntax_isOfKind(x_85, x_86);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_85);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_1);
x_88 = l_Lean_Macro_throwUnsupported___redArg(x_83);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_unsigned_to_nat(3u);
x_90 = lean_unsigned_to_nat(4u);
x_91 = l_Lean_Syntax_getArg(x_1, x_90);
x_92 = l_Lean_Syntax_isNone(x_91);
if (x_92 == 0)
{
uint8_t x_93; 
lean_inc(x_91);
x_93 = l_Lean_Syntax_matchesNull(x_91, x_80);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_91);
lean_dec(x_85);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_1);
x_94 = l_Lean_Macro_throwUnsupported___redArg(x_83);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = l_Lean_Syntax_getArg(x_91, x_35);
lean_dec(x_91);
x_96 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6;
lean_inc(x_95);
x_97 = l_Lean_Syntax_isOfKind(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_85);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_1);
x_98 = l_Lean_Macro_throwUnsupported___redArg(x_83);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Lean_Syntax_getArg(x_95, x_80);
lean_dec(x_95);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_58 = x_81;
x_59 = x_89;
x_60 = x_85;
x_61 = x_79;
x_62 = x_80;
x_63 = x_100;
x_64 = x_82;
x_65 = x_83;
goto block_78;
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_91);
x_101 = lean_box(0);
x_58 = x_81;
x_59 = x_89;
x_60 = x_85;
x_61 = x_79;
x_62 = x_80;
x_63 = x_101;
x_64 = x_82;
x_65 = x_83;
goto block_78;
}
}
}
block_119:
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_unsigned_to_nat(1u);
x_107 = l_Lean_Syntax_getArg(x_1, x_106);
x_108 = l_Lean_Syntax_isNone(x_107);
if (x_108 == 0)
{
uint8_t x_109; 
lean_inc(x_107);
x_109 = l_Lean_Syntax_matchesNull(x_107, x_106);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_107);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_1);
x_110 = l_Lean_Macro_throwUnsupported___redArg(x_105);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = l_Lean_Syntax_getArg(x_107, x_35);
lean_dec(x_107);
x_112 = l_Lean_Elab_Command_mkUnexpander___closed__12;
lean_inc(x_111);
x_113 = l_Lean_Syntax_isOfKind(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_111);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec(x_1);
x_114 = l_Lean_Macro_throwUnsupported___redArg(x_105);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = l_Lean_Syntax_getArg(x_111, x_106);
lean_dec(x_111);
x_116 = l_Lean_Syntax_getArgs(x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_79 = x_103;
x_80 = x_106;
x_81 = x_117;
x_82 = x_104;
x_83 = x_105;
goto block_102;
}
}
}
else
{
lean_object* x_118; 
lean_dec(x_107);
x_118 = lean_box(0);
x_79 = x_103;
x_80 = x_106;
x_81 = x_118;
x_82 = x_104;
x_83 = x_105;
goto block_102;
}
}
}
block_31:
{
lean_object* x_12; 
lean_inc_ref(x_10);
x_12 = l_Lean_Elab_toAttributeKind(x_6, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc_ref(x_10);
x_14 = l_Lean_Macro_getCurrNamespace(x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_unsigned_to_nat(7u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_unsigned_to_nat(9u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_22 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux(x_1, x_15, x_8, x_5, x_6, x_7, x_4, x_9, x_21, x_20, x_10, x_16);
lean_dec(x_1);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expandNotation", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__1;
x_2 = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8;
x_3 = l_Lean_Elab_Command_mkUnexpander___closed__8;
x_4 = l_Lean_Elab_Command_addInheritDocDefault___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__0;
x_3 = l_Lean_Elab_Command_expandNotation___closed__1;
x_4 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandNotation), 3, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = lean_unsigned_to_nat(152u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(158u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(46u);
x_4 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = lean_unsigned_to_nat(152u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = lean_unsigned_to_nat(152u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(50u);
x_4 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__5;
x_2 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__2;
x_3 = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Elab_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Notation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__0);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__1 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__1);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__2 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__2);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__3 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__3);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__4 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__4);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__5 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__5);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__6);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__0___redArg___closed__7);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__0 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__0);
l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__1 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Command_addInheritDocDefault_spec__1___redArg___closed__1);
l_Lean_Elab_Command_addInheritDocDefault___closed__0 = _init_l_Lean_Elab_Command_addInheritDocDefault___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_addInheritDocDefault___closed__0);
l_Lean_Elab_Command_addInheritDocDefault___closed__1 = _init_l_Lean_Elab_Command_addInheritDocDefault___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_addInheritDocDefault___closed__1);
l_Lean_Elab_Command_addInheritDocDefault___closed__2 = _init_l_Lean_Elab_Command_addInheritDocDefault___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_addInheritDocDefault___closed__2);
l_Lean_Elab_Command_addInheritDocDefault___closed__3 = _init_l_Lean_Elab_Command_addInheritDocDefault___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_addInheritDocDefault___closed__3);
l_Lean_Elab_Command_addInheritDocDefault___closed__4 = _init_l_Lean_Elab_Command_addInheritDocDefault___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_addInheritDocDefault___closed__4);
l_Lean_Elab_Command_addInheritDocDefault___closed__5 = _init_l_Lean_Elab_Command_addInheritDocDefault___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_addInheritDocDefault___closed__5);
l_Lean_Elab_Command_addInheritDocDefault___closed__6 = _init_l_Lean_Elab_Command_addInheritDocDefault___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_addInheritDocDefault___closed__6);
l_Lean_Elab_Command_addInheritDocDefault___closed__7 = _init_l_Lean_Elab_Command_addInheritDocDefault___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_addInheritDocDefault___closed__7);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13);
l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14 = _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14);
l_Lean_Elab_Command_removeParentheses___closed__0 = _init_l_Lean_Elab_Command_removeParentheses___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_removeParentheses___closed__0);
l_Lean_Elab_Command_removeParentheses___closed__1 = _init_l_Lean_Elab_Command_removeParentheses___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_removeParentheses___closed__1);
l_Lean_Elab_Command_removeParentheses___closed__2 = _init_l_Lean_Elab_Command_removeParentheses___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_removeParentheses___closed__2);
l_Lean_Elab_Command_removeParentheses___closed__3 = _init_l_Lean_Elab_Command_removeParentheses___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_removeParentheses___closed__3);
l_Lean_Elab_Command_removeParentheses___closed__4 = _init_l_Lean_Elab_Command_removeParentheses___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_removeParentheses___closed__4);
l_Lean_Elab_Command_removeParentheses___closed__5 = _init_l_Lean_Elab_Command_removeParentheses___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_removeParentheses___closed__5);
l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0 = _init_l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0();
lean_mark_persistent(l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0);
l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1 = _init_l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1();
lean_mark_persistent(l_Lean_Syntax_instForInTopDown_loop___at___Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1);
l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0 = _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0);
l_Lean_Elab_Command_mkUnexpander___closed__0 = _init_l_Lean_Elab_Command_mkUnexpander___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__0);
l_Lean_Elab_Command_mkUnexpander___closed__1 = _init_l_Lean_Elab_Command_mkUnexpander___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__1);
l_Lean_Elab_Command_mkUnexpander___closed__2 = _init_l_Lean_Elab_Command_mkUnexpander___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__2);
l_Lean_Elab_Command_mkUnexpander___closed__3 = _init_l_Lean_Elab_Command_mkUnexpander___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__3);
l_Lean_Elab_Command_mkUnexpander___closed__4 = _init_l_Lean_Elab_Command_mkUnexpander___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__4);
l_Lean_Elab_Command_mkUnexpander___closed__5 = _init_l_Lean_Elab_Command_mkUnexpander___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__5);
l_Lean_Elab_Command_mkUnexpander___closed__6 = _init_l_Lean_Elab_Command_mkUnexpander___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__6);
l_Lean_Elab_Command_mkUnexpander___closed__7 = _init_l_Lean_Elab_Command_mkUnexpander___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__7);
l_Lean_Elab_Command_mkUnexpander___closed__8 = _init_l_Lean_Elab_Command_mkUnexpander___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__8);
l_Lean_Elab_Command_mkUnexpander___closed__9 = _init_l_Lean_Elab_Command_mkUnexpander___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__9);
l_Lean_Elab_Command_mkUnexpander___closed__10 = _init_l_Lean_Elab_Command_mkUnexpander___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__10);
l_Lean_Elab_Command_mkUnexpander___closed__11 = _init_l_Lean_Elab_Command_mkUnexpander___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__11);
l_Lean_Elab_Command_mkUnexpander___closed__12 = _init_l_Lean_Elab_Command_mkUnexpander___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__12);
l_Lean_Elab_Command_mkUnexpander___closed__13 = _init_l_Lean_Elab_Command_mkUnexpander___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__13);
l_Lean_Elab_Command_mkUnexpander___closed__14 = _init_l_Lean_Elab_Command_mkUnexpander___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__14);
l_Lean_Elab_Command_mkUnexpander___closed__15 = _init_l_Lean_Elab_Command_mkUnexpander___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__15);
l_Lean_Elab_Command_mkUnexpander___closed__16 = _init_l_Lean_Elab_Command_mkUnexpander___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__16);
l_Lean_Elab_Command_mkUnexpander___closed__17 = _init_l_Lean_Elab_Command_mkUnexpander___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__17);
l_Lean_Elab_Command_mkUnexpander___closed__18 = _init_l_Lean_Elab_Command_mkUnexpander___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__18);
l_Lean_Elab_Command_mkUnexpander___closed__19 = _init_l_Lean_Elab_Command_mkUnexpander___closed__19();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__19);
l_Lean_Elab_Command_mkUnexpander___closed__20 = _init_l_Lean_Elab_Command_mkUnexpander___closed__20();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__20);
l_Lean_Elab_Command_mkUnexpander___closed__21 = _init_l_Lean_Elab_Command_mkUnexpander___closed__21();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__21);
l_Lean_Elab_Command_mkUnexpander___closed__22 = _init_l_Lean_Elab_Command_mkUnexpander___closed__22();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__22);
l_Lean_Elab_Command_mkUnexpander___closed__23 = _init_l_Lean_Elab_Command_mkUnexpander___closed__23();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__23);
l_Lean_Elab_Command_mkUnexpander___closed__24 = _init_l_Lean_Elab_Command_mkUnexpander___closed__24();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__24);
l_Lean_Elab_Command_mkUnexpander___closed__25 = _init_l_Lean_Elab_Command_mkUnexpander___closed__25();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__25);
l_Lean_Elab_Command_mkUnexpander___closed__26 = _init_l_Lean_Elab_Command_mkUnexpander___closed__26();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__26);
l_Lean_Elab_Command_mkUnexpander___closed__27 = _init_l_Lean_Elab_Command_mkUnexpander___closed__27();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__27);
l_Lean_Elab_Command_mkUnexpander___closed__28 = _init_l_Lean_Elab_Command_mkUnexpander___closed__28();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__28);
l_Lean_Elab_Command_mkUnexpander___closed__29 = _init_l_Lean_Elab_Command_mkUnexpander___closed__29();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__29);
l_Lean_Elab_Command_mkUnexpander___closed__30 = _init_l_Lean_Elab_Command_mkUnexpander___closed__30();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__30);
l_Lean_Elab_Command_mkUnexpander___closed__31 = _init_l_Lean_Elab_Command_mkUnexpander___closed__31();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__31);
l_Lean_Elab_Command_mkUnexpander___closed__32 = _init_l_Lean_Elab_Command_mkUnexpander___closed__32();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__32);
l_Lean_Elab_Command_mkUnexpander___closed__33 = _init_l_Lean_Elab_Command_mkUnexpander___closed__33();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__33);
l_Lean_Elab_Command_mkUnexpander___closed__34 = _init_l_Lean_Elab_Command_mkUnexpander___closed__34();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__34);
l_Lean_Elab_Command_mkUnexpander___closed__35 = _init_l_Lean_Elab_Command_mkUnexpander___closed__35();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__35);
l_Lean_Elab_Command_mkUnexpander___closed__36 = _init_l_Lean_Elab_Command_mkUnexpander___closed__36();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__36);
l_Lean_Elab_Command_mkUnexpander___closed__37 = _init_l_Lean_Elab_Command_mkUnexpander___closed__37();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__37);
l_Lean_Elab_Command_mkUnexpander___closed__38 = _init_l_Lean_Elab_Command_mkUnexpander___closed__38();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__38);
l_Lean_Elab_Command_mkUnexpander___closed__39 = _init_l_Lean_Elab_Command_mkUnexpander___closed__39();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__39);
l_Lean_Elab_Command_mkUnexpander___closed__40 = _init_l_Lean_Elab_Command_mkUnexpander___closed__40();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__40);
l_Lean_Elab_Command_mkUnexpander___closed__41 = _init_l_Lean_Elab_Command_mkUnexpander___closed__41();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__41);
l_Lean_Elab_Command_mkUnexpander___closed__42 = _init_l_Lean_Elab_Command_mkUnexpander___closed__42();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__42);
l_Lean_Elab_Command_mkUnexpander___closed__43 = _init_l_Lean_Elab_Command_mkUnexpander___closed__43();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__43);
l_Lean_Elab_Command_mkUnexpander___closed__44 = _init_l_Lean_Elab_Command_mkUnexpander___closed__44();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__44);
l_Lean_Elab_Command_mkUnexpander___closed__45 = _init_l_Lean_Elab_Command_mkUnexpander___closed__45();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__45);
l_Lean_Elab_Command_mkUnexpander___closed__46 = _init_l_Lean_Elab_Command_mkUnexpander___closed__46();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__46);
l_Lean_Elab_Command_mkUnexpander___closed__47 = _init_l_Lean_Elab_Command_mkUnexpander___closed__47();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__47);
l_Lean_Elab_Command_mkUnexpander___closed__48 = _init_l_Lean_Elab_Command_mkUnexpander___closed__48();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__48);
l_Lean_Elab_Command_mkUnexpander___closed__49 = _init_l_Lean_Elab_Command_mkUnexpander___closed__49();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__49);
l_Lean_Elab_Command_mkUnexpander___closed__50 = _init_l_Lean_Elab_Command_mkUnexpander___closed__50();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__50);
l_Lean_Elab_Command_mkUnexpander___closed__51 = _init_l_Lean_Elab_Command_mkUnexpander___closed__51();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__51);
l_Lean_Elab_Command_mkUnexpander___closed__52 = _init_l_Lean_Elab_Command_mkUnexpander___closed__52();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__52);
l_Lean_Elab_Command_mkUnexpander___closed__53 = _init_l_Lean_Elab_Command_mkUnexpander___closed__53();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__53);
l_Lean_Elab_Command_mkUnexpander___closed__54 = _init_l_Lean_Elab_Command_mkUnexpander___closed__54();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__54);
l_Lean_Elab_Command_mkUnexpander___closed__55 = _init_l_Lean_Elab_Command_mkUnexpander___closed__55();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__55);
l_Lean_Elab_Command_mkUnexpander___closed__56 = _init_l_Lean_Elab_Command_mkUnexpander___closed__56();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__56);
l_Lean_Elab_Command_mkUnexpander___closed__57 = _init_l_Lean_Elab_Command_mkUnexpander___closed__57();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__57);
l_Lean_Elab_Command_mkUnexpander___closed__58 = _init_l_Lean_Elab_Command_mkUnexpander___closed__58();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__58);
l_Lean_Elab_Command_mkUnexpander___closed__59 = _init_l_Lean_Elab_Command_mkUnexpander___closed__59();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__59);
l_Lean_Elab_Command_mkUnexpander___closed__60 = _init_l_Lean_Elab_Command_mkUnexpander___closed__60();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__60);
l_Lean_Elab_Command_mkUnexpander___closed__61 = _init_l_Lean_Elab_Command_mkUnexpander___closed__61();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__61);
l_Lean_Elab_Command_mkUnexpander___closed__62 = _init_l_Lean_Elab_Command_mkUnexpander___closed__62();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__62);
l_Lean_Elab_Command_mkUnexpander___closed__63 = _init_l_Lean_Elab_Command_mkUnexpander___closed__63();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__63);
l_Lean_Elab_Command_mkUnexpander___closed__64 = _init_l_Lean_Elab_Command_mkUnexpander___closed__64();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__64);
l_Lean_Elab_Command_mkUnexpander___closed__65 = _init_l_Lean_Elab_Command_mkUnexpander___closed__65();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__65);
l_Lean_Elab_Command_mkUnexpander___closed__66 = _init_l_Lean_Elab_Command_mkUnexpander___closed__66();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__66);
l_Lean_Elab_Command_mkUnexpander___closed__67 = _init_l_Lean_Elab_Command_mkUnexpander___closed__67();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__67);
l_Lean_Elab_Command_mkUnexpander___closed__68 = _init_l_Lean_Elab_Command_mkUnexpander___closed__68();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__68);
l_Lean_Elab_Command_mkUnexpander___closed__69 = _init_l_Lean_Elab_Command_mkUnexpander___closed__69();
lean_mark_persistent(l_Lean_Elab_Command_mkUnexpander___closed__69);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__0 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__0);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__1 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__1);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__2 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__2);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__3 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__3);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__4 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__4);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__5 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__5);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__6 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__6);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__7 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__7);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__8 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__8);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__9 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__9);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__10 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__10);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__11 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__11);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__12 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__12);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__13 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__13);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__14 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__14);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__15 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__15);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__16 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__16);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__17 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__17);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__18 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__18);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__19 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__19);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__20 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__20);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__21 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__21();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__21);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__22 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__22();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotationAux___closed__22);
l_Lean_Elab_Command_expandNotation___closed__0 = _init_l_Lean_Elab_Command_expandNotation___closed__0();
lean_mark_persistent(l_Lean_Elab_Command_expandNotation___closed__0);
l_Lean_Elab_Command_expandNotation___closed__1 = _init_l_Lean_Elab_Command_expandNotation___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandNotation___closed__1);
l_Lean_Elab_Command_expandNotation___closed__2 = _init_l_Lean_Elab_Command_expandNotation___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandNotation___closed__2);
l_Lean_Elab_Command_expandNotation___closed__3 = _init_l_Lean_Elab_Command_expandNotation___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandNotation___closed__3);
l_Lean_Elab_Command_expandNotation___closed__4 = _init_l_Lean_Elab_Command_expandNotation___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandNotation___closed__4);
l_Lean_Elab_Command_expandNotation___closed__5 = _init_l_Lean_Elab_Command_expandNotation___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandNotation___closed__5);
l_Lean_Elab_Command_expandNotation___closed__6 = _init_l_Lean_Elab_Command_expandNotation___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandNotation___closed__6);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__0 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__0);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__1 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__1);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__2 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1___closed__2);
if (builtin) {res = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__0 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__0);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__1 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__1);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__2 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__2);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__3 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__3);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__4 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__4);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__5 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__5);
l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__6 = _init_l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3___closed__6);
if (builtin) {res = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_expandNotation___regBuiltin_Lean_Elab_Command_expandNotation_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
