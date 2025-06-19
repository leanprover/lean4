// Lean compiler output
// Module: Lean.Elab.ErrorExplanation
// Imports: Lean.ErrorExplanation Lean.Meta.Eval Lean.Elab.Term Lean.Elab.Command Lean.Widget.UserWidget
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
lean_object* l_Lean_Name_getNumParts(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_ErrorExplanation_processDoc(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__2;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__1;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__2;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2;
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Term_addDotCompletionInfo___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__25;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__4;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6;
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__5;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20;
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
lean_object* l_Lean_MessageData_note(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__4;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__2(lean_object*);
static lean_object* l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__4;
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__1;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3;
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__1;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__9;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__1;
lean_object* l_Lean_Meta_evalExpr___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__4;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__8;
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_object* l_Lean_quoteNameMk(lean_object*);
static lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__5;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__7;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__5;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19;
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13;
lean_object* l_Lean_Elab_throwAbortTerm___at_Lean_Elab_Term_ensureType___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51;
lean_object* l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__3;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_errorDescriptionWidget;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22;
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35;
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47;
static lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__2;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__3;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__6;
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lean_getErrorExplanationRaw_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__2;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_ErrorExplanation_elabCheckedNamedError___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1;
lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5;
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__7;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabShowPanelWidgetsCmd___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8;
lean_object* l_Lean_log___at_Lean_Elab_Command_withLoggingExceptions___spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__10;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_withSetOptionIn___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__65;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__2;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
size_t lean_usize_land(size_t, size_t);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_ErrorExplanation_elabCheckedNamedError___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
extern lean_object* l_Lean_errorExplanationExt;
static lean_object* _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("errorDescriptionWidget", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__3;
x_3 = l_Lean_errorDescriptionWidget;
x_4 = l_Lean_Widget_addBuiltinModule(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwNamedErrorMacro", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwNamedErrorAtMacro", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedErrorMacro", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedErrorAtMacro", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedWarningMacro", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedWarningAtMacro", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.logNamedWarningAt", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedWarningAt", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quotedName", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termM!_", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("m!", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.logNamedWarning", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedWarning", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.logNamedErrorAt", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedErrorAt", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.logNamedError", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedError", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.throwNamedErrorAt", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwNamedErrorAt", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.throwNamedError", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwNamedError", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6;
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8;
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12;
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_matchesNull(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_unsigned_to_nat(4u);
x_29 = l_Lean_Syntax_getArg(x_1, x_28);
lean_dec(x_1);
x_30 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16;
lean_inc(x_29);
x_31 = l_Lean_Syntax_isOfKind(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_2, 5);
lean_inc(x_32);
x_33 = 0;
x_34 = l_Lean_SourceInfo_fromRef(x_32, x_33);
lean_dec(x_32);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_dec(x_2);
x_37 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22;
x_38 = l_Lean_addMacroScope(x_36, x_37, x_35);
x_39 = lean_box(0);
x_40 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20;
x_41 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24;
lean_inc(x_34);
x_42 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 3, x_41);
x_43 = l_Lean_Syntax_getId(x_21);
lean_dec(x_21);
lean_inc(x_43);
x_44 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_39, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = l_Lean_quoteNameMk(x_43);
x_46 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_34);
x_47 = l_Lean_Syntax_node3(x_34, x_46, x_19, x_45, x_29);
x_48 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_49 = l_Lean_Syntax_node2(x_34, x_48, x_42, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_3);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_43);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
x_52 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_53 = l_String_intercalate(x_52, x_51);
x_54 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = lean_box(2);
x_57 = l_Lean_Syntax_mkNameLit(x_55, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_39);
x_59 = lean_array_mk(x_58);
x_60 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_59);
x_62 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_34);
x_63 = l_Lean_Syntax_node3(x_34, x_62, x_19, x_61, x_29);
x_64 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_65 = l_Lean_Syntax_node2(x_34, x_64, x_42, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_67 = lean_ctor_get(x_2, 5);
lean_inc(x_67);
x_68 = 0;
x_69 = l_Lean_SourceInfo_fromRef(x_67, x_68);
lean_dec(x_67);
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
lean_dec(x_2);
x_72 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22;
x_73 = l_Lean_addMacroScope(x_71, x_72, x_70);
x_74 = lean_box(0);
x_75 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20;
x_76 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24;
lean_inc(x_69);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_76);
x_78 = l_Lean_Syntax_getId(x_21);
lean_dec(x_21);
lean_inc(x_78);
x_79 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_74, x_78);
x_80 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
lean_inc(x_69);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
lean_inc(x_69);
x_83 = l_Lean_Syntax_node2(x_69, x_82, x_81, x_29);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = l_Lean_quoteNameMk(x_78);
x_85 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_69);
x_86 = l_Lean_Syntax_node3(x_69, x_85, x_19, x_84, x_83);
x_87 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_88 = l_Lean_Syntax_node2(x_69, x_87, x_77, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_78);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
lean_dec(x_79);
x_91 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_92 = l_String_intercalate(x_91, x_90);
x_93 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = lean_box(2);
x_96 = l_Lean_Syntax_mkNameLit(x_94, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_74);
x_98 = lean_array_mk(x_97);
x_99 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_98);
x_101 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_69);
x_102 = l_Lean_Syntax_node3(x_69, x_101, x_19, x_100, x_83);
x_103 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_104 = l_Lean_Syntax_node2(x_69, x_103, x_77, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_3);
return x_105;
}
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_106 = lean_unsigned_to_nat(1u);
x_107 = l_Lean_Syntax_getArg(x_1, x_106);
x_108 = lean_unsigned_to_nat(2u);
x_109 = l_Lean_Syntax_getArg(x_1, x_108);
x_110 = lean_unsigned_to_nat(0u);
x_111 = l_Lean_Syntax_matchesNull(x_109, x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_107);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_box(1);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_3);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_unsigned_to_nat(3u);
x_115 = l_Lean_Syntax_getArg(x_1, x_114);
lean_dec(x_1);
x_116 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16;
lean_inc(x_115);
x_117 = l_Lean_Syntax_isOfKind(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_118 = lean_ctor_get(x_2, 5);
lean_inc(x_118);
x_119 = 0;
x_120 = l_Lean_SourceInfo_fromRef(x_118, x_119);
lean_dec(x_118);
x_121 = lean_ctor_get(x_2, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_2, 1);
lean_inc(x_122);
lean_dec(x_2);
x_123 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37;
x_124 = l_Lean_addMacroScope(x_122, x_123, x_121);
x_125 = lean_box(0);
x_126 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35;
x_127 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39;
lean_inc(x_120);
x_128 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_128, 0, x_120);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_128, 2, x_124);
lean_ctor_set(x_128, 3, x_127);
x_129 = l_Lean_Syntax_getId(x_107);
lean_dec(x_107);
lean_inc(x_129);
x_130 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_125, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = l_Lean_quoteNameMk(x_129);
x_132 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_120);
x_133 = l_Lean_Syntax_node2(x_120, x_132, x_131, x_115);
x_134 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_135 = l_Lean_Syntax_node2(x_120, x_134, x_128, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_3);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_129);
x_137 = lean_ctor_get(x_130, 0);
lean_inc(x_137);
lean_dec(x_130);
x_138 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_139 = l_String_intercalate(x_138, x_137);
x_140 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_141 = lean_string_append(x_140, x_139);
lean_dec(x_139);
x_142 = lean_box(2);
x_143 = l_Lean_Syntax_mkNameLit(x_141, x_142);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_125);
x_145 = lean_array_mk(x_144);
x_146 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_145);
x_148 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_120);
x_149 = l_Lean_Syntax_node2(x_120, x_148, x_147, x_115);
x_150 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_151 = l_Lean_Syntax_node2(x_120, x_150, x_128, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_3);
return x_152;
}
}
else
{
lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_153 = lean_ctor_get(x_2, 5);
lean_inc(x_153);
x_154 = 0;
x_155 = l_Lean_SourceInfo_fromRef(x_153, x_154);
lean_dec(x_153);
x_156 = lean_ctor_get(x_2, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_dec(x_2);
x_158 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37;
x_159 = l_Lean_addMacroScope(x_157, x_158, x_156);
x_160 = lean_box(0);
x_161 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35;
x_162 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39;
lean_inc(x_155);
x_163 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_161);
lean_ctor_set(x_163, 2, x_159);
lean_ctor_set(x_163, 3, x_162);
x_164 = l_Lean_Syntax_getId(x_107);
lean_dec(x_107);
lean_inc(x_164);
x_165 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_160, x_164);
x_166 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
lean_inc(x_155);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_155);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
lean_inc(x_155);
x_169 = l_Lean_Syntax_node2(x_155, x_168, x_167, x_115);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_170 = l_Lean_quoteNameMk(x_164);
x_171 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_155);
x_172 = l_Lean_Syntax_node2(x_155, x_171, x_170, x_169);
x_173 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_174 = l_Lean_Syntax_node2(x_155, x_173, x_163, x_172);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_3);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_164);
x_176 = lean_ctor_get(x_165, 0);
lean_inc(x_176);
lean_dec(x_165);
x_177 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_178 = l_String_intercalate(x_177, x_176);
x_179 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_180 = lean_string_append(x_179, x_178);
lean_dec(x_178);
x_181 = lean_box(2);
x_182 = l_Lean_Syntax_mkNameLit(x_180, x_181);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_160);
x_184 = lean_array_mk(x_183);
x_185 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_186 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_185);
lean_ctor_set(x_186, 2, x_184);
x_187 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_155);
x_188 = l_Lean_Syntax_node2(x_155, x_187, x_186, x_169);
x_189 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_190 = l_Lean_Syntax_node2(x_155, x_189, x_163, x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_3);
return x_191;
}
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_192 = lean_unsigned_to_nat(1u);
x_193 = l_Lean_Syntax_getArg(x_1, x_192);
x_194 = lean_unsigned_to_nat(2u);
x_195 = l_Lean_Syntax_getArg(x_1, x_194);
x_196 = lean_unsigned_to_nat(3u);
x_197 = l_Lean_Syntax_getArg(x_1, x_196);
x_198 = lean_unsigned_to_nat(0u);
x_199 = l_Lean_Syntax_matchesNull(x_197, x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_box(1);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_3);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_202 = lean_unsigned_to_nat(4u);
x_203 = l_Lean_Syntax_getArg(x_1, x_202);
lean_dec(x_1);
x_204 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16;
lean_inc(x_203);
x_205 = l_Lean_Syntax_isOfKind(x_203, x_204);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_206 = lean_ctor_get(x_2, 5);
lean_inc(x_206);
x_207 = 0;
x_208 = l_Lean_SourceInfo_fromRef(x_206, x_207);
lean_dec(x_206);
x_209 = lean_ctor_get(x_2, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_2, 1);
lean_inc(x_210);
lean_dec(x_2);
x_211 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43;
x_212 = l_Lean_addMacroScope(x_210, x_211, x_209);
x_213 = lean_box(0);
x_214 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41;
x_215 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45;
lean_inc(x_208);
x_216 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_216, 0, x_208);
lean_ctor_set(x_216, 1, x_214);
lean_ctor_set(x_216, 2, x_212);
lean_ctor_set(x_216, 3, x_215);
x_217 = l_Lean_Syntax_getId(x_195);
lean_dec(x_195);
lean_inc(x_217);
x_218 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_213, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_219 = l_Lean_quoteNameMk(x_217);
x_220 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_208);
x_221 = l_Lean_Syntax_node3(x_208, x_220, x_193, x_219, x_203);
x_222 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_223 = l_Lean_Syntax_node2(x_208, x_222, x_216, x_221);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_3);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_217);
x_225 = lean_ctor_get(x_218, 0);
lean_inc(x_225);
lean_dec(x_218);
x_226 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_227 = l_String_intercalate(x_226, x_225);
x_228 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_229 = lean_string_append(x_228, x_227);
lean_dec(x_227);
x_230 = lean_box(2);
x_231 = l_Lean_Syntax_mkNameLit(x_229, x_230);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_213);
x_233 = lean_array_mk(x_232);
x_234 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_235 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_235, 0, x_230);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set(x_235, 2, x_233);
x_236 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_208);
x_237 = l_Lean_Syntax_node3(x_208, x_236, x_193, x_235, x_203);
x_238 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_239 = l_Lean_Syntax_node2(x_208, x_238, x_216, x_237);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_3);
return x_240;
}
}
else
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_241 = lean_ctor_get(x_2, 5);
lean_inc(x_241);
x_242 = 0;
x_243 = l_Lean_SourceInfo_fromRef(x_241, x_242);
lean_dec(x_241);
x_244 = lean_ctor_get(x_2, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_2, 1);
lean_inc(x_245);
lean_dec(x_2);
x_246 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43;
x_247 = l_Lean_addMacroScope(x_245, x_246, x_244);
x_248 = lean_box(0);
x_249 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41;
x_250 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45;
lean_inc(x_243);
x_251 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_249);
lean_ctor_set(x_251, 2, x_247);
lean_ctor_set(x_251, 3, x_250);
x_252 = l_Lean_Syntax_getId(x_195);
lean_dec(x_195);
lean_inc(x_252);
x_253 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_248, x_252);
x_254 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
lean_inc(x_243);
x_255 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_255, 0, x_243);
lean_ctor_set(x_255, 1, x_254);
x_256 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
lean_inc(x_243);
x_257 = l_Lean_Syntax_node2(x_243, x_256, x_255, x_203);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_258 = l_Lean_quoteNameMk(x_252);
x_259 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_243);
x_260 = l_Lean_Syntax_node3(x_243, x_259, x_193, x_258, x_257);
x_261 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_262 = l_Lean_Syntax_node2(x_243, x_261, x_251, x_260);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_3);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_252);
x_264 = lean_ctor_get(x_253, 0);
lean_inc(x_264);
lean_dec(x_253);
x_265 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_266 = l_String_intercalate(x_265, x_264);
x_267 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_268 = lean_string_append(x_267, x_266);
lean_dec(x_266);
x_269 = lean_box(2);
x_270 = l_Lean_Syntax_mkNameLit(x_268, x_269);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_248);
x_272 = lean_array_mk(x_271);
x_273 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_274 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set(x_274, 2, x_272);
x_275 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_243);
x_276 = l_Lean_Syntax_node3(x_243, x_275, x_193, x_274, x_257);
x_277 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_278 = l_Lean_Syntax_node2(x_243, x_277, x_251, x_276);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_3);
return x_279;
}
}
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_280 = lean_unsigned_to_nat(1u);
x_281 = l_Lean_Syntax_getArg(x_1, x_280);
x_282 = lean_unsigned_to_nat(2u);
x_283 = l_Lean_Syntax_getArg(x_1, x_282);
x_284 = lean_unsigned_to_nat(0u);
x_285 = l_Lean_Syntax_matchesNull(x_283, x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_281);
lean_dec(x_2);
lean_dec(x_1);
x_286 = lean_box(1);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_3);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_288 = lean_unsigned_to_nat(3u);
x_289 = l_Lean_Syntax_getArg(x_1, x_288);
lean_dec(x_1);
x_290 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16;
lean_inc(x_289);
x_291 = l_Lean_Syntax_isOfKind(x_289, x_290);
if (x_291 == 0)
{
lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_292 = lean_ctor_get(x_2, 5);
lean_inc(x_292);
x_293 = 0;
x_294 = l_Lean_SourceInfo_fromRef(x_292, x_293);
lean_dec(x_292);
x_295 = lean_ctor_get(x_2, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_2, 1);
lean_inc(x_296);
lean_dec(x_2);
x_297 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49;
x_298 = l_Lean_addMacroScope(x_296, x_297, x_295);
x_299 = lean_box(0);
x_300 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47;
x_301 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51;
lean_inc(x_294);
x_302 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_302, 0, x_294);
lean_ctor_set(x_302, 1, x_300);
lean_ctor_set(x_302, 2, x_298);
lean_ctor_set(x_302, 3, x_301);
x_303 = l_Lean_Syntax_getId(x_281);
lean_dec(x_281);
lean_inc(x_303);
x_304 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_299, x_303);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_305 = l_Lean_quoteNameMk(x_303);
x_306 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_294);
x_307 = l_Lean_Syntax_node2(x_294, x_306, x_305, x_289);
x_308 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_309 = l_Lean_Syntax_node2(x_294, x_308, x_302, x_307);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_3);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_303);
x_311 = lean_ctor_get(x_304, 0);
lean_inc(x_311);
lean_dec(x_304);
x_312 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_313 = l_String_intercalate(x_312, x_311);
x_314 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_315 = lean_string_append(x_314, x_313);
lean_dec(x_313);
x_316 = lean_box(2);
x_317 = l_Lean_Syntax_mkNameLit(x_315, x_316);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_299);
x_319 = lean_array_mk(x_318);
x_320 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_321 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_321, 0, x_316);
lean_ctor_set(x_321, 1, x_320);
lean_ctor_set(x_321, 2, x_319);
x_322 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_294);
x_323 = l_Lean_Syntax_node2(x_294, x_322, x_321, x_289);
x_324 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_325 = l_Lean_Syntax_node2(x_294, x_324, x_302, x_323);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_3);
return x_326;
}
}
else
{
lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_327 = lean_ctor_get(x_2, 5);
lean_inc(x_327);
x_328 = 0;
x_329 = l_Lean_SourceInfo_fromRef(x_327, x_328);
lean_dec(x_327);
x_330 = lean_ctor_get(x_2, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_2, 1);
lean_inc(x_331);
lean_dec(x_2);
x_332 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49;
x_333 = l_Lean_addMacroScope(x_331, x_332, x_330);
x_334 = lean_box(0);
x_335 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47;
x_336 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51;
lean_inc(x_329);
x_337 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_337, 0, x_329);
lean_ctor_set(x_337, 1, x_335);
lean_ctor_set(x_337, 2, x_333);
lean_ctor_set(x_337, 3, x_336);
x_338 = l_Lean_Syntax_getId(x_281);
lean_dec(x_281);
lean_inc(x_338);
x_339 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_334, x_338);
x_340 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
lean_inc(x_329);
x_341 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_341, 0, x_329);
lean_ctor_set(x_341, 1, x_340);
x_342 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
lean_inc(x_329);
x_343 = l_Lean_Syntax_node2(x_329, x_342, x_341, x_289);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_344 = l_Lean_quoteNameMk(x_338);
x_345 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_329);
x_346 = l_Lean_Syntax_node2(x_329, x_345, x_344, x_343);
x_347 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_348 = l_Lean_Syntax_node2(x_329, x_347, x_337, x_346);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_3);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_338);
x_350 = lean_ctor_get(x_339, 0);
lean_inc(x_350);
lean_dec(x_339);
x_351 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_352 = l_String_intercalate(x_351, x_350);
x_353 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_354 = lean_string_append(x_353, x_352);
lean_dec(x_352);
x_355 = lean_box(2);
x_356 = l_Lean_Syntax_mkNameLit(x_354, x_355);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_334);
x_358 = lean_array_mk(x_357);
x_359 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_360 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_360, 0, x_355);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set(x_360, 2, x_358);
x_361 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_329);
x_362 = l_Lean_Syntax_node2(x_329, x_361, x_360, x_343);
x_363 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_364 = l_Lean_Syntax_node2(x_329, x_363, x_337, x_362);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_3);
return x_365;
}
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_366 = lean_unsigned_to_nat(1u);
x_367 = l_Lean_Syntax_getArg(x_1, x_366);
x_368 = lean_unsigned_to_nat(2u);
x_369 = l_Lean_Syntax_getArg(x_1, x_368);
x_370 = lean_unsigned_to_nat(3u);
x_371 = l_Lean_Syntax_getArg(x_1, x_370);
x_372 = lean_unsigned_to_nat(0u);
x_373 = l_Lean_Syntax_matchesNull(x_371, x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_2);
lean_dec(x_1);
x_374 = lean_box(1);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_3);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
x_376 = lean_unsigned_to_nat(4u);
x_377 = l_Lean_Syntax_getArg(x_1, x_376);
lean_dec(x_1);
x_378 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16;
lean_inc(x_377);
x_379 = l_Lean_Syntax_isOfKind(x_377, x_378);
if (x_379 == 0)
{
lean_object* x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_380 = lean_ctor_get(x_2, 5);
lean_inc(x_380);
x_381 = 0;
x_382 = l_Lean_SourceInfo_fromRef(x_380, x_381);
lean_dec(x_380);
x_383 = lean_ctor_get(x_2, 2);
lean_inc(x_383);
x_384 = lean_ctor_get(x_2, 1);
lean_inc(x_384);
lean_dec(x_2);
x_385 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55;
x_386 = l_Lean_addMacroScope(x_384, x_385, x_383);
x_387 = lean_box(0);
x_388 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53;
x_389 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57;
lean_inc(x_382);
x_390 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_390, 0, x_382);
lean_ctor_set(x_390, 1, x_388);
lean_ctor_set(x_390, 2, x_386);
lean_ctor_set(x_390, 3, x_389);
x_391 = l_Lean_Syntax_getId(x_369);
lean_dec(x_369);
lean_inc(x_391);
x_392 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_387, x_391);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_393 = l_Lean_quoteNameMk(x_391);
x_394 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_382);
x_395 = l_Lean_Syntax_node3(x_382, x_394, x_367, x_393, x_377);
x_396 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_397 = l_Lean_Syntax_node2(x_382, x_396, x_390, x_395);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_3);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_391);
x_399 = lean_ctor_get(x_392, 0);
lean_inc(x_399);
lean_dec(x_392);
x_400 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_401 = l_String_intercalate(x_400, x_399);
x_402 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_403 = lean_string_append(x_402, x_401);
lean_dec(x_401);
x_404 = lean_box(2);
x_405 = l_Lean_Syntax_mkNameLit(x_403, x_404);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_387);
x_407 = lean_array_mk(x_406);
x_408 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_409 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_409, 0, x_404);
lean_ctor_set(x_409, 1, x_408);
lean_ctor_set(x_409, 2, x_407);
x_410 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_382);
x_411 = l_Lean_Syntax_node3(x_382, x_410, x_367, x_409, x_377);
x_412 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_413 = l_Lean_Syntax_node2(x_382, x_412, x_390, x_411);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_3);
return x_414;
}
}
else
{
lean_object* x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_415 = lean_ctor_get(x_2, 5);
lean_inc(x_415);
x_416 = 0;
x_417 = l_Lean_SourceInfo_fromRef(x_415, x_416);
lean_dec(x_415);
x_418 = lean_ctor_get(x_2, 2);
lean_inc(x_418);
x_419 = lean_ctor_get(x_2, 1);
lean_inc(x_419);
lean_dec(x_2);
x_420 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55;
x_421 = l_Lean_addMacroScope(x_419, x_420, x_418);
x_422 = lean_box(0);
x_423 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53;
x_424 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57;
lean_inc(x_417);
x_425 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_425, 0, x_417);
lean_ctor_set(x_425, 1, x_423);
lean_ctor_set(x_425, 2, x_421);
lean_ctor_set(x_425, 3, x_424);
x_426 = l_Lean_Syntax_getId(x_369);
lean_dec(x_369);
lean_inc(x_426);
x_427 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_422, x_426);
x_428 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
lean_inc(x_417);
x_429 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_429, 0, x_417);
lean_ctor_set(x_429, 1, x_428);
x_430 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
lean_inc(x_417);
x_431 = l_Lean_Syntax_node2(x_417, x_430, x_429, x_377);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_432 = l_Lean_quoteNameMk(x_426);
x_433 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_417);
x_434 = l_Lean_Syntax_node3(x_417, x_433, x_367, x_432, x_431);
x_435 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_436 = l_Lean_Syntax_node2(x_417, x_435, x_425, x_434);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_3);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_426);
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
lean_dec(x_427);
x_439 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_440 = l_String_intercalate(x_439, x_438);
x_441 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_442 = lean_string_append(x_441, x_440);
lean_dec(x_440);
x_443 = lean_box(2);
x_444 = l_Lean_Syntax_mkNameLit(x_442, x_443);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_422);
x_446 = lean_array_mk(x_445);
x_447 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_448 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_447);
lean_ctor_set(x_448, 2, x_446);
x_449 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_417);
x_450 = l_Lean_Syntax_node3(x_417, x_449, x_367, x_448, x_431);
x_451 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_452 = l_Lean_Syntax_node2(x_417, x_451, x_425, x_450);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_3);
return x_453;
}
}
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_454 = lean_unsigned_to_nat(1u);
x_455 = l_Lean_Syntax_getArg(x_1, x_454);
x_456 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59;
lean_inc(x_455);
x_457 = l_Lean_Syntax_isOfKind(x_455, x_456);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_458 = lean_unsigned_to_nat(2u);
x_459 = l_Lean_Syntax_getArg(x_1, x_458);
x_460 = lean_unsigned_to_nat(0u);
x_461 = l_Lean_Syntax_matchesNull(x_459, x_460);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; 
lean_dec(x_455);
lean_dec(x_2);
lean_dec(x_1);
x_462 = lean_box(1);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_3);
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_464 = lean_unsigned_to_nat(3u);
x_465 = l_Lean_Syntax_getArg(x_1, x_464);
lean_dec(x_1);
x_466 = lean_ctor_get(x_2, 5);
lean_inc(x_466);
x_467 = 0;
x_468 = l_Lean_SourceInfo_fromRef(x_466, x_467);
lean_dec(x_466);
x_469 = lean_ctor_get(x_2, 2);
lean_inc(x_469);
x_470 = lean_ctor_get(x_2, 1);
lean_inc(x_470);
lean_dec(x_2);
x_471 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63;
x_472 = l_Lean_addMacroScope(x_470, x_471, x_469);
x_473 = lean_box(0);
x_474 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61;
x_475 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__65;
lean_inc(x_468);
x_476 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_476, 0, x_468);
lean_ctor_set(x_476, 1, x_474);
lean_ctor_set(x_476, 2, x_472);
lean_ctor_set(x_476, 3, x_475);
x_477 = l_Lean_Syntax_getId(x_455);
lean_dec(x_455);
lean_inc(x_477);
x_478 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_473, x_477);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_479 = l_Lean_quoteNameMk(x_477);
x_480 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_468);
x_481 = l_Lean_Syntax_node2(x_468, x_480, x_479, x_465);
x_482 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_483 = l_Lean_Syntax_node2(x_468, x_482, x_476, x_481);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_3);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_477);
x_485 = lean_ctor_get(x_478, 0);
lean_inc(x_485);
lean_dec(x_478);
x_486 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_487 = l_String_intercalate(x_486, x_485);
x_488 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_489 = lean_string_append(x_488, x_487);
lean_dec(x_487);
x_490 = lean_box(2);
x_491 = l_Lean_Syntax_mkNameLit(x_489, x_490);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_473);
x_493 = lean_array_mk(x_492);
x_494 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_495 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_495, 0, x_490);
lean_ctor_set(x_495, 1, x_494);
lean_ctor_set(x_495, 2, x_493);
x_496 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_468);
x_497 = l_Lean_Syntax_node2(x_468, x_496, x_495, x_465);
x_498 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_499 = l_Lean_Syntax_node2(x_468, x_498, x_476, x_497);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_3);
return x_500;
}
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; 
x_501 = lean_unsigned_to_nat(2u);
x_502 = l_Lean_Syntax_getArg(x_1, x_501);
x_503 = lean_unsigned_to_nat(0u);
x_504 = l_Lean_Syntax_matchesNull(x_502, x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
lean_dec(x_455);
lean_dec(x_2);
lean_dec(x_1);
x_505 = lean_box(1);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_3);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; 
x_507 = lean_unsigned_to_nat(3u);
x_508 = l_Lean_Syntax_getArg(x_1, x_507);
lean_dec(x_1);
x_509 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16;
lean_inc(x_508);
x_510 = l_Lean_Syntax_isOfKind(x_508, x_509);
if (x_510 == 0)
{
lean_object* x_511; uint8_t x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_511 = lean_ctor_get(x_2, 5);
lean_inc(x_511);
x_512 = 0;
x_513 = l_Lean_SourceInfo_fromRef(x_511, x_512);
lean_dec(x_511);
x_514 = lean_ctor_get(x_2, 2);
lean_inc(x_514);
x_515 = lean_ctor_get(x_2, 1);
lean_inc(x_515);
lean_dec(x_2);
x_516 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63;
x_517 = l_Lean_addMacroScope(x_515, x_516, x_514);
x_518 = lean_box(0);
x_519 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61;
x_520 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__65;
lean_inc(x_513);
x_521 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_521, 0, x_513);
lean_ctor_set(x_521, 1, x_519);
lean_ctor_set(x_521, 2, x_517);
lean_ctor_set(x_521, 3, x_520);
x_522 = l_Lean_Syntax_getId(x_455);
lean_dec(x_455);
lean_inc(x_522);
x_523 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_518, x_522);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_524 = l_Lean_quoteNameMk(x_522);
x_525 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_513);
x_526 = l_Lean_Syntax_node2(x_513, x_525, x_524, x_508);
x_527 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_528 = l_Lean_Syntax_node2(x_513, x_527, x_521, x_526);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_3);
return x_529;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_522);
x_530 = lean_ctor_get(x_523, 0);
lean_inc(x_530);
lean_dec(x_523);
x_531 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_532 = l_String_intercalate(x_531, x_530);
x_533 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_534 = lean_string_append(x_533, x_532);
lean_dec(x_532);
x_535 = lean_box(2);
x_536 = l_Lean_Syntax_mkNameLit(x_534, x_535);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_518);
x_538 = lean_array_mk(x_537);
x_539 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_540 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_539);
lean_ctor_set(x_540, 2, x_538);
x_541 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_513);
x_542 = l_Lean_Syntax_node2(x_513, x_541, x_540, x_508);
x_543 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_544 = l_Lean_Syntax_node2(x_513, x_543, x_521, x_542);
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_3);
return x_545;
}
}
else
{
lean_object* x_546; uint8_t x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_546 = lean_ctor_get(x_2, 5);
lean_inc(x_546);
x_547 = 0;
x_548 = l_Lean_SourceInfo_fromRef(x_546, x_547);
lean_dec(x_546);
x_549 = lean_ctor_get(x_2, 2);
lean_inc(x_549);
x_550 = lean_ctor_get(x_2, 1);
lean_inc(x_550);
lean_dec(x_2);
x_551 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63;
x_552 = l_Lean_addMacroScope(x_550, x_551, x_549);
x_553 = lean_box(0);
x_554 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61;
x_555 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__65;
lean_inc(x_548);
x_556 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_556, 0, x_548);
lean_ctor_set(x_556, 1, x_554);
lean_ctor_set(x_556, 2, x_552);
lean_ctor_set(x_556, 3, x_555);
x_557 = l_Lean_Syntax_getId(x_455);
lean_dec(x_455);
lean_inc(x_557);
x_558 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_553, x_557);
x_559 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
lean_inc(x_548);
x_560 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_560, 0, x_548);
lean_ctor_set(x_560, 1, x_559);
x_561 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
lean_inc(x_548);
x_562 = l_Lean_Syntax_node2(x_548, x_561, x_560, x_508);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_563 = l_Lean_quoteNameMk(x_557);
x_564 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_548);
x_565 = l_Lean_Syntax_node2(x_548, x_564, x_563, x_562);
x_566 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_567 = l_Lean_Syntax_node2(x_548, x_566, x_556, x_565);
x_568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_3);
return x_568;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec(x_557);
x_569 = lean_ctor_get(x_558, 0);
lean_inc(x_569);
lean_dec(x_558);
x_570 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_571 = l_String_intercalate(x_570, x_569);
x_572 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_573 = lean_string_append(x_572, x_571);
lean_dec(x_571);
x_574 = lean_box(2);
x_575 = l_Lean_Syntax_mkNameLit(x_573, x_574);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_553);
x_577 = lean_array_mk(x_576);
x_578 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
x_579 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_579, 0, x_574);
lean_ctor_set(x_579, 1, x_578);
lean_ctor_set(x_579, 2, x_577);
x_580 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
lean_inc(x_548);
x_581 = l_Lean_Syntax_node2(x_548, x_580, x_579, x_562);
x_582 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_583 = l_Lean_Syntax_node2(x_548, x_582, x_556, x_581);
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_583);
lean_ctor_set(x_584, 1, x_3);
return x_584;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Name_hash___override(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__4(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__5(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__5(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_array_get_size(x_15);
x_17 = l_Lean_Name_hash___override(x_11);
x_18 = 32;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = 16;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_26 = 1;
x_27 = lean_usize_sub(x_25, x_26);
x_28 = lean_usize_land(x_24, x_27);
x_29 = lean_array_uget(x_15, x_28);
x_30 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__1(x_11, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_14, x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_12);
lean_ctor_set(x_33, 2, x_29);
x_34 = lean_array_uset(x_15, x_28, x_33);
x_35 = lean_unsigned_to_nat(4u);
x_36 = lean_nat_mul(x_32, x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = lean_nat_div(x_36, x_37);
lean_dec(x_36);
x_39 = lean_array_get_size(x_34);
x_40 = lean_nat_dec_le(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__2(x_34);
lean_ctor_set(x_7, 1, x_41);
lean_ctor_set(x_7, 0, x_32);
x_6 = x_10;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_32);
x_6 = x_10;
x_8 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc(x_3);
x_44 = lean_array_uset(x_15, x_28, x_3);
x_45 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__5(x_11, x_12, x_29);
x_46 = lean_array_uset(x_44, x_28, x_45);
lean_ctor_set(x_7, 1, x_46);
x_6 = x_10;
x_8 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; size_t x_58; size_t x_59; size_t x_60; size_t x_61; size_t x_62; lean_object* x_63; uint8_t x_64; 
x_48 = lean_ctor_get(x_7, 0);
x_49 = lean_ctor_get(x_7, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_7);
x_50 = lean_array_get_size(x_49);
x_51 = l_Lean_Name_hash___override(x_11);
x_52 = 32;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = 16;
x_56 = lean_uint64_shift_right(x_54, x_55);
x_57 = lean_uint64_xor(x_54, x_56);
x_58 = lean_uint64_to_usize(x_57);
x_59 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_60 = 1;
x_61 = lean_usize_sub(x_59, x_60);
x_62 = lean_usize_land(x_58, x_61);
x_63 = lean_array_uget(x_49, x_62);
x_64 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__1(x_11, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_48, x_65);
lean_dec(x_48);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_11);
lean_ctor_set(x_67, 1, x_12);
lean_ctor_set(x_67, 2, x_63);
x_68 = lean_array_uset(x_49, x_62, x_67);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_nat_mul(x_66, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_nat_div(x_70, x_71);
lean_dec(x_70);
x_73 = lean_array_get_size(x_68);
x_74 = lean_nat_dec_le(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__2(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_75);
x_6 = x_10;
x_7 = x_76;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_66);
lean_ctor_set(x_78, 1, x_68);
x_6 = x_10;
x_7 = x_78;
x_8 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_3);
x_80 = lean_array_uset(x_49, x_62, x_3);
x_81 = l_Std_DHashMap_Internal_AssocList_replace___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__5(x_11, x_12, x_63);
x_82 = lean_array_uset(x_80, x_62, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_48);
lean_ctor_set(x_83, 1, x_82);
x_6 = x_10;
x_7 = x_83;
x_8 = lean_box(0);
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Exception", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Log", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22;
x_4 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__25;
x_5 = l_List_forIn_x27_loop___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__6(x_3, x_1, x_2, x_4, x_3, x_3, x_4, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_ErrorExplanation_elabCheckedNamedError___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro), 3, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_8);
lean_inc(x_4);
x_12 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__9(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = l_Lean_Elab_Term_elabTerm(x_13, x_2, x_15, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("There is no explanation associated with the name `", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`. Add an explanation of this error to the `Lean.ErrorExplanations` module.", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The error name `", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` was removed in Lean version ", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" and should not be used.", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_194; uint8_t x_195; 
x_194 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6;
lean_inc(x_1);
x_195 = l_Lean_Syntax_isOfKind(x_1, x_194);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10;
lean_inc(x_1);
x_197 = l_Lean_Syntax_isOfKind(x_1, x_196);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14;
lean_inc(x_1);
x_199 = l_Lean_Syntax_isOfKind(x_1, x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_unsigned_to_nat(1u);
x_201 = l_Lean_Syntax_getArg(x_1, x_200);
x_202 = lean_unsigned_to_nat(4u);
x_11 = x_201;
x_12 = x_202;
goto block_193;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_unsigned_to_nat(2u);
x_204 = l_Lean_Syntax_getArg(x_1, x_203);
x_205 = lean_unsigned_to_nat(5u);
x_11 = x_204;
x_12 = x_205;
goto block_193;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_unsigned_to_nat(2u);
x_207 = l_Lean_Syntax_getArg(x_1, x_206);
x_208 = lean_unsigned_to_nat(5u);
x_11 = x_207;
x_12 = x_208;
goto block_193;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_unsigned_to_nat(2u);
x_210 = l_Lean_Syntax_getArg(x_1, x_209);
x_211 = lean_unsigned_to_nat(5u);
x_11 = x_210;
x_12 = x_211;
goto block_193;
}
block_193:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = l_Lean_Syntax_getNumArgs(x_1);
x_14 = lean_nat_dec_eq(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_13);
lean_inc(x_1);
x_15 = x_1;
goto block_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_186 = l_Lean_Syntax_getArgs(x_1);
x_187 = lean_unsigned_to_nat(1u);
x_188 = lean_nat_sub(x_13, x_187);
lean_dec(x_13);
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Array_toSubarray___rarg(x_186, x_189, x_188);
x_191 = l_Array_ofSubarray___rarg(x_190);
lean_dec(x_190);
lean_inc(x_1);
x_192 = l_Lean_Syntax_setArgs(x_1, x_191);
x_15 = x_192;
goto block_185;
}
block_185:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = l_Lean_Syntax_getNumArgs(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = l_Lean_Syntax_getArg(x_15, x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Term_addDotCompletionInfo___spec__1(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Lean_Syntax_getId(x_11);
x_26 = lean_erase_macro_scopes(x_25);
lean_inc(x_26);
lean_inc(x_11);
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_11);
x_27 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_27, 0, x_21);
x_28 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_st_ref_get(x_9, x_30);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_getErrorExplanationRaw_x3f(x_36, x_26);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = l_Lean_MessageData_ofName(x_26);
x_39 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__2;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_38);
lean_ctor_set(x_32, 0, x_39);
x_40 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__4;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_40);
lean_ctor_set(x_28, 0, x_32);
x_41 = 2;
x_42 = 0;
lean_inc(x_8);
x_43 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_11, x_28, x_41, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_11);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_free_object(x_32);
lean_free_object(x_28);
lean_dec(x_26);
lean_dec(x_11);
x_50 = lean_box(0);
x_51 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_MessageData_ofName(x_26);
x_54 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__6;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_53);
lean_ctor_set(x_32, 0, x_54);
x_55 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__8;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_55);
lean_ctor_set(x_28, 0, x_32);
x_56 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_28);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__10;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = 1;
x_61 = 0;
lean_inc(x_8);
x_62 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_11, x_59, x_60, x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_11);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_64);
lean_dec(x_63);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_32, 0);
x_67 = lean_ctor_get(x_32, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_32);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_getErrorExplanationRaw_x3f(x_68, x_26);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = l_Lean_MessageData_ofName(x_26);
x_71 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__2;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__4;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_73);
lean_ctor_set(x_28, 0, x_72);
x_74 = 2;
x_75 = 0;
lean_inc(x_8);
x_76 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_11, x_28, x_74, x_75, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
lean_dec(x_11);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_77, x_4, x_5, x_6, x_7, x_8, x_9, x_78);
lean_dec(x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
lean_dec(x_69);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 2);
lean_inc(x_82);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_free_object(x_28);
lean_dec(x_26);
lean_dec(x_11);
x_83 = lean_box(0);
x_84 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_83, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec(x_82);
x_86 = l_Lean_MessageData_ofName(x_26);
x_87 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__6;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__8;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_89);
lean_ctor_set(x_28, 0, x_88);
x_90 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_28);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__10;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = 1;
x_95 = 0;
lean_inc(x_8);
x_96 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_11, x_93, x_94, x_95, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
lean_dec(x_11);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_97, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
lean_dec(x_97);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_28, 1);
lean_inc(x_100);
lean_dec(x_28);
x_101 = lean_st_ref_get(x_9, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec(x_102);
x_106 = l_Lean_getErrorExplanationRaw_x3f(x_105, x_26);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_107 = l_Lean_MessageData_ofName(x_26);
x_108 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__2;
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(7, 2, 0);
} else {
 x_109 = x_104;
 lean_ctor_set_tag(x_109, 7);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__4;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = 2;
x_113 = 0;
lean_inc(x_8);
x_114 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_11, x_111, x_112, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_103);
lean_dec(x_11);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_115, x_4, x_5, x_6, x_7, x_8, x_9, x_116);
lean_dec(x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_106, 0);
lean_inc(x_118);
lean_dec(x_106);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_ctor_get(x_119, 2);
lean_inc(x_120);
lean_dec(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_104);
lean_dec(x_26);
lean_dec(x_11);
x_121 = lean_box(0);
x_122 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_121, x_4, x_5, x_6, x_7, x_8, x_9, x_103);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
lean_dec(x_120);
x_124 = l_Lean_MessageData_ofName(x_26);
x_125 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__6;
if (lean_is_scalar(x_104)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_104;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__8;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_stringToMessageData(x_123);
lean_dec(x_123);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__10;
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = 1;
x_134 = 0;
lean_inc(x_8);
x_135 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_11, x_132, x_133, x_134, x_4, x_5, x_6, x_7, x_8, x_9, x_103);
lean_dec(x_11);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_136, x_4, x_5, x_6, x_7, x_8, x_9, x_137);
lean_dec(x_136);
return x_138;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_139 = lean_ctor_get(x_21, 1);
lean_inc(x_139);
lean_dec(x_21);
x_140 = l_Lean_Syntax_getId(x_11);
x_141 = lean_erase_macro_scopes(x_140);
lean_inc(x_141);
lean_inc(x_11);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_11);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(x_143, x_4, x_5, x_6, x_7, x_8, x_9, x_139);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
x_147 = lean_st_ref_get(x_9, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
x_152 = l_Lean_getErrorExplanationRaw_x3f(x_151, x_141);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_153 = l_Lean_MessageData_ofName(x_141);
x_154 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__2;
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(7, 2, 0);
} else {
 x_155 = x_150;
 lean_ctor_set_tag(x_155, 7);
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__4;
if (lean_is_scalar(x_146)) {
 x_157 = lean_alloc_ctor(7, 2, 0);
} else {
 x_157 = x_146;
 lean_ctor_set_tag(x_157, 7);
}
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = 2;
x_159 = 0;
lean_inc(x_8);
x_160 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_11, x_157, x_158, x_159, x_4, x_5, x_6, x_7, x_8, x_9, x_149);
lean_dec(x_11);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_161, x_4, x_5, x_6, x_7, x_8, x_9, x_162);
lean_dec(x_161);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_152, 0);
lean_inc(x_164);
lean_dec(x_152);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_ctor_get(x_165, 2);
lean_inc(x_166);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_150);
lean_dec(x_146);
lean_dec(x_141);
lean_dec(x_11);
x_167 = lean_box(0);
x_168 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_167, x_4, x_5, x_6, x_7, x_8, x_9, x_149);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
lean_dec(x_166);
x_170 = l_Lean_MessageData_ofName(x_141);
x_171 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__6;
if (lean_is_scalar(x_150)) {
 x_172 = lean_alloc_ctor(7, 2, 0);
} else {
 x_172 = x_150;
 lean_ctor_set_tag(x_172, 7);
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__8;
if (lean_is_scalar(x_146)) {
 x_174 = lean_alloc_ctor(7, 2, 0);
} else {
 x_174 = x_146;
 lean_ctor_set_tag(x_174, 7);
}
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Lean_stringToMessageData(x_169);
lean_dec(x_169);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__10;
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = 1;
x_180 = 0;
lean_inc(x_8);
x_181 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_11, x_178, x_179, x_180, x_4, x_5, x_6, x_7, x_8, x_9, x_149);
lean_dec(x_11);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_182, x_4, x_5, x_6, x_7, x_8, x_9, x_183);
lean_dec(x_182);
return x_184;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The constant `", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has not been imported", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Add `import ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` to this file's header to use this macro", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_Lean_Syntax_getKind(x_1);
x_11 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_array_get_size(x_13);
x_16 = l_Lean_Name_hash___override(x_10);
x_17 = 32;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = 16;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_25 = 1;
x_26 = lean_usize_sub(x_24, x_25);
x_27 = lean_usize_land(x_23, x_26);
x_28 = lean_array_uget(x_13, x_27);
lean_dec(x_13);
x_29 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_ErrorExplanation_elabCheckedNamedError___spec__1(x_10, x_28);
lean_dec(x_28);
lean_dec(x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_11);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2(x_1, x_2, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_st_ref_get(x_8, x_9);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 1;
lean_inc(x_35);
x_42 = l_Lean_Environment_contains(x_40, x_35, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = l_Lean_MessageData_ofName(x_35);
x_44 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_43);
lean_ctor_set(x_36, 0, x_44);
x_45 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_45);
lean_ctor_set(x_32, 0, x_36);
x_46 = l_Lean_MessageData_ofName(x_34);
x_47 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_46);
lean_ctor_set(x_11, 0, x_47);
x_48 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_11);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_hint_x27(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_32);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_36);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_11);
x_57 = lean_box(0);
x_58 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2(x_1, x_2, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_36, 0);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_36);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = 1;
lean_inc(x_35);
x_63 = l_Lean_Environment_contains(x_61, x_35, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_2);
lean_dec(x_1);
x_64 = l_Lean_MessageData_ofName(x_35);
x_65 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4;
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_67);
lean_ctor_set(x_32, 0, x_66);
x_68 = l_Lean_MessageData_ofName(x_34);
x_69 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_68);
lean_ctor_set(x_11, 0, x_69);
x_70 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_11);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_MessageData_hint_x27(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_32);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
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
else
{
lean_object* x_79; lean_object* x_80; 
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_11);
x_79 = lean_box(0);
x_80 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2(x_1, x_2, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_81 = lean_ctor_get(x_32, 0);
x_82 = lean_ctor_get(x_32, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_32);
x_83 = lean_st_ref_get(x_8, x_9);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
x_88 = 1;
lean_inc(x_82);
x_89 = l_Lean_Environment_contains(x_87, x_82, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_2);
lean_dec(x_1);
x_90 = l_Lean_MessageData_ofName(x_82);
x_91 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2;
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(7, 2, 0);
} else {
 x_92 = x_86;
 lean_ctor_set_tag(x_92, 7);
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_MessageData_ofName(x_81);
x_96 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6;
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_95);
lean_ctor_set(x_11, 0, x_96);
x_97 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_11);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_MessageData_hint_x27(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_100, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_81);
lean_free_object(x_11);
x_106 = lean_box(0);
x_107 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2(x_1, x_2, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; size_t x_117; size_t x_118; size_t x_119; size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; 
x_108 = lean_ctor_get(x_11, 1);
lean_inc(x_108);
lean_dec(x_11);
x_109 = lean_array_get_size(x_108);
x_110 = l_Lean_Name_hash___override(x_10);
x_111 = 32;
x_112 = lean_uint64_shift_right(x_110, x_111);
x_113 = lean_uint64_xor(x_110, x_112);
x_114 = 16;
x_115 = lean_uint64_shift_right(x_113, x_114);
x_116 = lean_uint64_xor(x_113, x_115);
x_117 = lean_uint64_to_usize(x_116);
x_118 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_119 = 1;
x_120 = lean_usize_sub(x_118, x_119);
x_121 = lean_usize_land(x_117, x_120);
x_122 = lean_array_uget(x_108, x_121);
lean_dec(x_108);
x_123 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_ErrorExplanation_elabCheckedNamedError___spec__1(x_10, x_122);
lean_dec(x_122);
lean_dec(x_10);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_box(0);
x_125 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2(x_1, x_2, x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; 
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_st_ref_get(x_8, x_9);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
lean_dec(x_131);
x_135 = 1;
lean_inc(x_128);
x_136 = l_Lean_Environment_contains(x_134, x_128, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_2);
lean_dec(x_1);
x_137 = l_Lean_MessageData_ofName(x_128);
x_138 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2;
if (lean_is_scalar(x_133)) {
 x_139 = lean_alloc_ctor(7, 2, 0);
} else {
 x_139 = x_133;
 lean_ctor_set_tag(x_139, 7);
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4;
if (lean_is_scalar(x_129)) {
 x_141 = lean_alloc_ctor(7, 2, 0);
} else {
 x_141 = x_129;
 lean_ctor_set_tag(x_141, 7);
}
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_MessageData_ofName(x_127);
x_143 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8;
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_MessageData_hint_x27(x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_148, x_3, x_4, x_5, x_6, x_7, x_8, x_132);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_133);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_154 = lean_box(0);
x_155 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2(x_1, x_2, x_154, x_3, x_4, x_5, x_6, x_7, x_8, x_132);
return x_155;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_ErrorExplanation_elabCheckedNamedError___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Elab_ErrorExplanation_elabCheckedNamedError___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ErrorExplanation", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabCheckedNamedError", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_termElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lean_Meta_evalExpr___rarg(x_1, x_2, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
lean_inc(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Elab_Term_elabTerm(x_1, x_10, x_11, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_hasSyntheticSorry(x_13);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 1;
x_17 = l_Lean_Meta_evalExpr___rarg(x_2, x_13, x_16, x_5, x_6, x_7, x_8, x_14);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_18 = l_Lean_Elab_throwAbortTerm___at_Lean_Elab_Term_ensureType___spec__1___rarg(x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_7, x_6);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_14 = lean_array_uget(x_5, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_dec(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = 2;
x_20 = 0;
lean_inc(x_9);
x_21 = l_Lean_log___at_Lean_Elab_Command_withLoggingExceptions___spec__4(x_18, x_19, x_20, x_9, x_10, x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_7, x_23);
x_25 = lean_box(0);
x_7 = x_24;
x_8 = x_25;
x_11 = x_22;
goto _start;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_nat_add(x_31, x_29);
x_33 = lean_nat_add(x_31, x_30);
x_34 = 0;
x_35 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_34);
x_36 = lean_string_utf8_extract(x_1, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
lean_ctor_set_tag(x_15, 2);
lean_ctor_set(x_15, 1, x_36);
lean_ctor_set(x_15, 0, x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_27);
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = 2;
lean_inc(x_9);
x_40 = l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(x_15, x_38, x_39, x_34, x_9, x_10, x_11);
lean_dec(x_15);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = 1;
x_43 = lean_usize_add(x_7, x_42);
x_44 = lean_box(0);
x_7 = x_43;
x_8 = x_44;
x_11 = x_41;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_nat_add(x_48, x_46);
x_50 = lean_nat_add(x_48, x_47);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_51);
x_53 = lean_string_utf8_extract(x_1, x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_27);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = 2;
lean_inc(x_9);
x_58 = l_Lean_logAt___at_Lean_Elab_Command_withLoggingExceptions___spec__3(x_54, x_56, x_57, x_51, x_9, x_10, x_11);
lean_dec(x_54);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = 1;
x_61 = lean_usize_add(x_7, x_60);
x_62 = lean_box(0);
x_7 = x_61;
x_8 = x_62;
x_11 = x_59;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = l_Lean_TSyntax_getDocString(x_1);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_Syntax_getHeadInfo_x3f(x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
x_6 = x_24;
goto block_20;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 0;
x_27 = l_Lean_SourceInfo_getPos_x3f(x_25, x_26);
lean_dec(x_25);
x_6 = x_27;
goto block_20;
}
block_20:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_5);
x_7 = l_Lean_rewriteManualLinksCore(x_5, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_array_size(x_10);
x_13 = 0;
x_14 = lean_box(0);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__2(x_5, x_6, x_10, x_11, x_10, x_12, x_13, x_14, x_2, x_3, x_9);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
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
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_12, x_8, x_2, x_3, x_13);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_10, 1, x_17);
lean_ctor_set(x_10, 0, x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_20, x_8, x_2, x_3, x_21);
lean_dec(x_2);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_25;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_throwError___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__5(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
x_20 = lean_ctor_get(x_3, 8);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_9);
lean_ctor_set(x_22, 7, x_19);
lean_ctor_set(x_22, 8, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*9, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__5(x_2, x_22, x_4, x_8);
return x_23;
}
}
}
static lean_object* _init_l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected doc string", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
if (lean_obj_tag(x_6) == 2)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_string_utf8_byte_size(x_8);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_string_utf8_extract(x_8, x_13, x_12);
lean_dec(x_12);
lean_dec(x_8);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_string_utf8_byte_size(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_string_utf8_extract(x_15, x_19, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = l_Lean_MessageData_ofSyntax(x_6);
x_23 = l_Lean_indentD(x_22);
x_24 = l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__2;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__4;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__4(x_1, x_27, x_2, x_3, x_4);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_throwError___at_Lean_withSetOptionIn___spec__7(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
x_20 = lean_ctor_get(x_3, 8);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_17);
lean_ctor_set(x_22, 5, x_18);
lean_ctor_set(x_22, 6, x_9);
lean_ctor_set(x_22, 7, x_19);
lean_ctor_set(x_22, 8, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*9, x_21);
x_23 = l_Lean_throwError___at_Lean_withSetOptionIn___spec__7(x_2, x_22, x_4, x_8);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_errorExplanationExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_take(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_3);
x_15 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1;
x_16 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_15, x_13, x_8);
lean_ctor_set(x_10, 0, x_16);
x_17 = lean_st_ref_set(x_6, x_10, x_12);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
x_27 = lean_ctor_get(x_10, 2);
x_28 = lean_ctor_get(x_10, 3);
x_29 = lean_ctor_get(x_10, 4);
x_30 = lean_ctor_get(x_10, 5);
x_31 = lean_ctor_get(x_10, 6);
x_32 = lean_ctor_get(x_10, 7);
x_33 = lean_ctor_get(x_10, 8);
x_34 = lean_ctor_get(x_10, 9);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_8, 1, x_35);
lean_ctor_set(x_8, 0, x_3);
x_36 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1;
x_37 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_36, x_25, x_8);
x_38 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_28);
lean_ctor_set(x_38, 4, x_29);
lean_ctor_set(x_38, 5, x_30);
lean_ctor_set(x_38, 6, x_31);
lean_ctor_set(x_38, 7, x_32);
lean_ctor_set(x_38, 8, x_33);
lean_ctor_set(x_38, 9, x_34);
x_39 = lean_st_ref_set(x_6, x_38, x_24);
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
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_8);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 5);
lean_inc(x_51);
x_52 = lean_ctor_get(x_44, 6);
lean_inc(x_52);
x_53 = lean_ctor_get(x_44, 7);
lean_inc(x_53);
x_54 = lean_ctor_get(x_44, 8);
lean_inc(x_54);
x_55 = lean_ctor_get(x_44, 9);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 lean_ctor_release(x_44, 4);
 lean_ctor_release(x_44, 5);
 lean_ctor_release(x_44, 6);
 lean_ctor_release(x_44, 7);
 lean_ctor_release(x_44, 8);
 lean_ctor_release(x_44, 9);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_2);
lean_ctor_set(x_57, 2, x_4);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_3);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1;
x_60 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_59, x_46, x_58);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 10, 0);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_47);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_49);
lean_ctor_set(x_61, 4, x_50);
lean_ctor_set(x_61, 5, x_51);
lean_ctor_set(x_61, 6, x_52);
lean_ctor_set(x_61, 7, x_53);
lean_ctor_set(x_61, 8, x_54);
lean_ctor_set(x_61, 9, x_55);
x_62 = lean_st_ref_set(x_6, x_61, x_45);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = 0;
x_11 = l_Lean_Syntax_getPos_x3f(x_4, x_10);
x_12 = l_Lean_Syntax_getTailPos_x3f(x_4, x_10);
x_13 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_16, x_16);
lean_ctor_set(x_13, 1, x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_19 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_18, x_6, x_7, x_15);
lean_dec(x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_22, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_25, x_6, x_7, x_21);
lean_dec(x_6);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_13, 1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_31, x_29);
lean_dec(x_29);
lean_ctor_set(x_13, 1, x_32);
lean_ctor_set(x_12, 0, x_13);
x_33 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_12, x_6, x_7, x_30);
lean_dec(x_6);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_37, x_34);
lean_dec(x_34);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_12, 0, x_39);
x_40 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_12, x_6, x_7, x_36);
lean_dec(x_6);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_12, 0);
lean_inc(x_41);
lean_dec(x_12);
x_42 = lean_ctor_get(x_13, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_44 = x_13;
} else {
 lean_dec_ref(x_13);
 x_44 = lean_box(0);
}
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_45, x_41);
lean_dec(x_41);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_48, x_6, x_7, x_43);
lean_dec(x_6);
return x_49;
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_11);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_13, 1);
x_54 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_52, x_52);
lean_dec(x_52);
lean_ctor_set(x_13, 1, x_54);
lean_ctor_set(x_11, 0, x_13);
x_55 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_11, x_6, x_7, x_53);
lean_dec(x_6);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_11, 0);
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_56, x_56);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_11, 0, x_60);
x_61 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_11, x_6, x_7, x_58);
lean_dec(x_6);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_11, 0);
lean_inc(x_62);
lean_dec(x_11);
x_63 = lean_ctor_get(x_13, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_65 = x_13;
} else {
 lean_dec_ref(x_13);
 x_65 = lean_box(0);
}
x_66 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_62, x_62);
lean_dec(x_62);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_68, x_6, x_7, x_64);
lean_dec(x_6);
return x_69;
}
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_11, 0);
lean_inc(x_70);
lean_dec(x_11);
x_71 = !lean_is_exclusive(x_12);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_13);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_12, 0);
x_74 = lean_ctor_get(x_13, 1);
x_75 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_70, x_73);
lean_dec(x_73);
lean_dec(x_70);
lean_ctor_set(x_13, 1, x_75);
lean_ctor_set(x_12, 0, x_13);
x_76 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_12, x_6, x_7, x_74);
lean_dec(x_6);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_12, 0);
x_78 = lean_ctor_get(x_13, 0);
x_79 = lean_ctor_get(x_13, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_13);
x_80 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_70, x_77);
lean_dec(x_77);
lean_dec(x_70);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_12, 0, x_81);
x_82 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_12, x_6, x_7, x_79);
lean_dec(x_6);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_12, 0);
lean_inc(x_83);
lean_dec(x_12);
x_84 = lean_ctor_get(x_13, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_13, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_86 = x_13;
} else {
 lean_dec_ref(x_13);
 x_86 = lean_box(0);
}
x_87 = l_Lean_DeclarationRange_ofStringPositions(x_9, x_70, x_83);
lean_dec(x_83);
lean_dec(x_70);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_89, x_6, x_7, x_85);
lean_dec(x_6);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_ErrorExplanation_processDoc(x_1);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_5, x_16);
x_18 = 0;
x_19 = l_Lean_Syntax_getRange_x3f(x_17, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_12);
lean_dec(x_14);
lean_ctor_set_tag(x_10, 3);
lean_ctor_set(x_10, 0, x_15);
x_20 = l_Lean_MessageData_ofFormat(x_10);
x_21 = l_Lean_throwError___at_Lean_withSetOptionIn___spec__7(x_20, x_7, x_8, x_9);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_10);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = l_Lean_FileMap_toPosition(x_28, x_29);
lean_dec(x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_dec(x_33);
x_34 = lean_nat_add(x_32, x_14);
lean_dec(x_14);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
lean_inc(x_34);
lean_ctor_set(x_30, 1, x_35);
lean_ctor_set(x_30, 0, x_34);
lean_inc(x_28);
x_36 = l_Lean_FileMap_ofPosition(x_28, x_30);
x_37 = lean_nat_add(x_34, x_16);
lean_dec(x_34);
lean_ctor_set(x_12, 1, x_35);
lean_ctor_set(x_12, 0, x_37);
x_38 = l_Lean_FileMap_ofPosition(x_28, x_12);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = 1;
x_41 = l_Lean_Syntax_ofRange(x_39, x_40);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 0, x_15);
x_42 = l_Lean_MessageData_ofFormat(x_19);
x_43 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_41, x_42, x_7, x_8, x_9);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_ctor_get(x_30, 0);
lean_inc(x_48);
lean_dec(x_30);
x_49 = lean_nat_add(x_48, x_14);
lean_dec(x_14);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(0u);
lean_inc(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_28);
x_52 = l_Lean_FileMap_ofPosition(x_28, x_51);
x_53 = lean_nat_add(x_49, x_16);
lean_dec(x_49);
lean_ctor_set(x_12, 1, x_50);
lean_ctor_set(x_12, 0, x_53);
x_54 = l_Lean_FileMap_ofPosition(x_28, x_12);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = 1;
x_57 = l_Lean_Syntax_ofRange(x_55, x_56);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 0, x_15);
x_58 = l_Lean_MessageData_ofFormat(x_19);
x_59 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_57, x_58, x_7, x_8, x_9);
lean_dec(x_57);
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
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
lean_dec(x_19);
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_65);
x_67 = l_Lean_FileMap_toPosition(x_65, x_66);
lean_dec(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_nat_add(x_68, x_14);
lean_dec(x_14);
lean_dec(x_68);
x_71 = lean_unsigned_to_nat(0u);
lean_inc(x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_65);
x_73 = l_Lean_FileMap_ofPosition(x_65, x_72);
x_74 = lean_nat_add(x_70, x_16);
lean_dec(x_70);
lean_ctor_set(x_12, 1, x_71);
lean_ctor_set(x_12, 0, x_74);
x_75 = l_Lean_FileMap_ofPosition(x_65, x_12);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = 1;
x_78 = l_Lean_Syntax_ofRange(x_76, x_77);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_15);
x_80 = l_Lean_MessageData_ofFormat(x_79);
x_81 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_78, x_80, x_7, x_8, x_9);
lean_dec(x_78);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_12, 0);
x_87 = lean_ctor_get(x_12, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_12);
x_88 = lean_unsigned_to_nat(1u);
x_89 = l_Lean_Syntax_getArg(x_5, x_88);
x_90 = 0;
x_91 = l_Lean_Syntax_getRange_x3f(x_89, x_90);
lean_dec(x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_86);
lean_ctor_set_tag(x_10, 3);
lean_ctor_set(x_10, 0, x_87);
x_92 = l_Lean_MessageData_ofFormat(x_10);
x_93 = l_Lean_throwError___at_Lean_withSetOptionIn___spec__7(x_92, x_7, x_8, x_9);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_free_object(x_10);
x_98 = lean_ctor_get(x_91, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_99 = x_91;
} else {
 lean_dec_ref(x_91);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_7, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
lean_dec(x_98);
lean_inc(x_100);
x_102 = l_Lean_FileMap_toPosition(x_100, x_101);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_nat_add(x_103, x_86);
lean_dec(x_86);
lean_dec(x_103);
x_106 = lean_unsigned_to_nat(0u);
lean_inc(x_105);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
lean_inc(x_100);
x_108 = l_Lean_FileMap_ofPosition(x_100, x_107);
x_109 = lean_nat_add(x_105, x_88);
lean_dec(x_105);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_106);
x_111 = l_Lean_FileMap_ofPosition(x_100, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
x_113 = 1;
x_114 = l_Lean_Syntax_ofRange(x_112, x_113);
if (lean_is_scalar(x_99)) {
 x_115 = lean_alloc_ctor(3, 1, 0);
} else {
 x_115 = x_99;
 lean_ctor_set_tag(x_115, 3);
}
lean_ctor_set(x_115, 0, x_87);
x_116 = l_Lean_MessageData_ofFormat(x_115);
x_117 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_114, x_116, x_7, x_8, x_9);
lean_dec(x_114);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_10, 0);
lean_inc(x_122);
lean_dec(x_10);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = lean_unsigned_to_nat(1u);
x_127 = l_Lean_Syntax_getArg(x_5, x_126);
x_128 = 0;
x_129 = l_Lean_Syntax_getRange_x3f(x_127, x_128);
lean_dec(x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_125);
lean_dec(x_123);
x_130 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_130, 0, x_124);
x_131 = l_Lean_MessageData_ofFormat(x_130);
x_132 = l_Lean_throwError___at_Lean_withSetOptionIn___spec__7(x_131, x_7, x_8, x_9);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_137 = lean_ctor_get(x_129, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_138 = x_129;
} else {
 lean_dec_ref(x_129);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_7, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
lean_dec(x_137);
lean_inc(x_139);
x_141 = l_Lean_FileMap_toPosition(x_139, x_140);
lean_dec(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_nat_add(x_142, x_123);
lean_dec(x_123);
lean_dec(x_142);
x_145 = lean_unsigned_to_nat(0u);
lean_inc(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_inc(x_139);
x_147 = l_Lean_FileMap_ofPosition(x_139, x_146);
x_148 = lean_nat_add(x_144, x_126);
lean_dec(x_144);
if (lean_is_scalar(x_125)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_125;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
x_150 = l_Lean_FileMap_ofPosition(x_139, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_150);
x_152 = 1;
x_153 = l_Lean_Syntax_ofRange(x_151, x_152);
if (lean_is_scalar(x_138)) {
 x_154 = lean_alloc_ctor(3, 1, 0);
} else {
 x_154 = x_138;
 lean_ctor_set_tag(x_154, 3);
}
lean_ctor_set(x_154, 0, x_124);
x_155 = l_Lean_MessageData_ofFormat(x_154);
x_156 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_153, x_155, x_7, x_8, x_9);
lean_dec(x_153);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_10);
x_161 = lean_box(0);
x_162 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__3(x_1, x_2, x_3, x_4, x_161, x_7, x_8, x_9);
return x_162;
}
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot add explanation: An error explanation already exists for `", 65, 65);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_6);
x_9 = l_Lean_validateDocComment___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__1(x_1, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_inc(x_6);
x_13 = l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3(x_1, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_7, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_Lean_errorExplanationExt;
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*3);
lean_dec(x_23);
x_25 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1;
x_26 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_21, x_25, x_20, x_24);
x_27 = l_Lean_NameMap_contains___rarg(x_26, x_3);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_16);
lean_free_object(x_9);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__4(x_14, x_2, x_3, x_4, x_1, x_28, x_6, x_7, x_19);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_2);
x_30 = l_Lean_MessageData_ofName(x_3);
x_31 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__2;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_30);
lean_ctor_set(x_16, 0, x_31);
x_32 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__3;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_32);
lean_ctor_set(x_9, 0, x_16);
x_33 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_4, x_9, x_6, x_7, x_19);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = l_Lean_errorExplanationExt;
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_43, sizeof(void*)*3);
lean_dec(x_43);
x_45 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1;
x_46 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_41, x_45, x_40, x_44);
x_47 = l_Lean_NameMap_contains___rarg(x_46, x_3);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_free_object(x_9);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__4(x_14, x_2, x_3, x_4, x_1, x_48, x_6, x_7, x_39);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_14);
lean_dec(x_2);
x_50 = l_Lean_MessageData_ofName(x_3);
x_51 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__2;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__3;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_53);
lean_ctor_set(x_9, 0, x_52);
x_54 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_4, x_9, x_6, x_7, x_39);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_free_object(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_13);
if (x_59 == 0)
{
return x_13;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_13, 0);
x_61 = lean_ctor_get(x_13, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_13);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_9, 1);
lean_inc(x_63);
lean_dec(x_9);
lean_inc(x_6);
x_64 = l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3(x_1, x_6, x_7, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_7, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_box(0);
x_73 = l_Lean_errorExplanationExt;
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_74, sizeof(void*)*3);
lean_dec(x_74);
x_76 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1;
x_77 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_72, x_76, x_71, x_75);
x_78 = l_Lean_NameMap_contains___rarg(x_77, x_3);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_70);
x_79 = lean_box(0);
x_80 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__4(x_65, x_2, x_3, x_4, x_1, x_79, x_6, x_7, x_69);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_65);
lean_dec(x_2);
x_81 = l_Lean_MessageData_ofName(x_3);
x_82 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__2;
if (lean_is_scalar(x_70)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_70;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__3;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_4, x_85, x_6, x_7, x_69);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
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
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_ctor_get(x_64, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_93 = x_64;
} else {
 lean_dec_ref(x_64);
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
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid name `", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`: Error explanation names must have two components", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The first component of an error explanation name identifies the package from which the error originates, and the second identifies the error itself.", 148, 148);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__6;
x_2 = l_Lean_MessageData_note(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Name_getNumParts(x_3);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_2);
x_12 = l_Lean_MessageData_ofName(x_3);
x_13 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__7;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_4, x_18, x_6, x_7, x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5(x_1, x_2, x_3, x_4, x_24, x_6, x_7, x_8);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`: Error explanations cannot have inaccessible names. This error often occurs when an error explanation is generated using a macro.", 131, 131);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Name_hasMacroScopes(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_4);
x_12 = l_Lean_MessageData_ofSyntax(x_4);
x_13 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_4, x_16, x_6, x_7, x_8);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Metadata", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
x_3 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid name for error explanation: `", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__3;
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__1___boxed), 10, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Elab_Command_runTermElabM___rarg(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Syntax_getId(x_2);
x_14 = l_Lean_Name_isAnonymous(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7(x_3, x_11, x_13, x_2, x_15, x_5, x_6, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_17 = l_Lean_MessageData_ofSyntax(x_2);
x_18 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__5;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_2, x_21, x_5, x_6, x_12);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
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
lean_dec(x_5);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("registerErrorExplanationStx", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1;
x_4 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("docComment", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1;
x_4 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("To use this command, add `import Lean.ErrorExplanation` to the header of this file", 82, 82);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabShowPanelWidgetsCmd___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabShowPanelWidgetsCmd___spec__1___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59;
lean_inc(x_16);
x_18 = l_Lean_Syntax_isOfKind(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabShowPanelWidgetsCmd___spec__1___rarg(x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_22 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_replaceRef(x_14, x_23);
lean_dec(x_23);
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_2, 6);
lean_dec(x_27);
lean_ctor_set(x_2, 6, x_25);
x_28 = lean_st_ref_get(x_3, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6;
x_33 = 1;
x_34 = l_Lean_Environment_contains(x_31, x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_9);
x_35 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8;
x_36 = l_Lean_throwError___at_Lean_withSetOptionIn___spec__7(x_35, x_2, x_3, x_30);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8(x_21, x_16, x_9, x_41, x_2, x_3, x_30);
lean_dec(x_9);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_ctor_get(x_2, 3);
x_47 = lean_ctor_get(x_2, 4);
x_48 = lean_ctor_get(x_2, 5);
x_49 = lean_ctor_get(x_2, 7);
x_50 = lean_ctor_get(x_2, 8);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_52 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_45);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_47);
lean_ctor_set(x_52, 5, x_48);
lean_ctor_set(x_52, 6, x_25);
lean_ctor_set(x_52, 7, x_49);
lean_ctor_set(x_52, 8, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*9, x_51);
x_53 = lean_st_ref_get(x_3, x_24);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6;
x_58 = 1;
x_59 = l_Lean_Environment_contains(x_56, x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_9);
x_60 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8;
x_61 = l_Lean_throwError___at_Lean_withSetOptionIn___spec__7(x_60, x_52, x_3, x_55);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8(x_21, x_16, x_9, x_66, x_52, x_3, x_55);
lean_dec(x_9);
return x_67;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__2(x_1, x_2, x_3, x_4, x_5, x_12, x_13, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_validateDocComment___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabRegisterErrorExplanation", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
x_4 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__3;
x_3 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3;
x_4 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2;
x_5 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_ErrorExplanation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ErrorExplanation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ErrorExplanation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_UserWidget(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1 = _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1();
lean_mark_persistent(l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1);
l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2 = _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2();
lean_mark_persistent(l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2);
l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__3 = _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__3();
lean_mark_persistent(l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__3);
if (builtin) {res = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__65 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__65();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__65);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__25 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__25();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__25);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__1);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__2);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__3 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__3);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__4 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__4);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__5 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__5);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__6 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__6);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__7 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__7);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__8 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__8);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__9 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__9);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__10 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___lambda__2___closed__10);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__5);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__6);
if (builtin) {res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__1 = _init_l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__1();
lean_mark_persistent(l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__1);
l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__2 = _init_l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__2();
lean_mark_persistent(l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__2);
l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__3 = _init_l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__3();
lean_mark_persistent(l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__3);
l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__4 = _init_l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__4();
lean_mark_persistent(l_Lean_getDocStringText___at_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___spec__3___closed__4);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__2___closed__1);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__1);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__2);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__3 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__5___closed__3);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__1);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__2);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__3 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__3);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__4 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__4);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__5 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__5();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__5);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__6 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__6();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__6);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__7 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__7();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__6___closed__7);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__1);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__7___closed__2);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__1);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__2);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__3 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__3);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__4 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__4();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__4);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__5 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__5();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lambda__8___closed__5);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__3 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__3);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__4 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__4();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__4);
if (builtin) {res = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
