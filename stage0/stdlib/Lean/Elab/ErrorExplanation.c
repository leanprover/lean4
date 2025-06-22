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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2;
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4;
lean_object* l_Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15;
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_NameMap_contains___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__25;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6;
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Std_Data_DTreeMap_Internal_Lemmas_0__Std_DTreeMap_Internal_Impl_modifyMap_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20;
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
lean_object* l_Lean_MessageData_note(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9;
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwMVarError_spec__0___redArg(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3;
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
static lean_object* l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
lean_object* l_Lean_instQuoteNameMkStr1___private__1(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DTreeMap_Internal_Lemmas_0__Std_DTreeMap_Internal_Impl_modifyMap_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10;
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DTreeMap_Internal_Lemmas_0__Std_DTreeMap_Internal_Impl_modifyMap_spec__1___redArg(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
static lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3;
static lean_object* l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__3;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6;
lean_object* l_Array_ofSubarray___redArg(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10;
static lean_object* l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__2;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13;
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__24;
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5;
extern lean_object* l_Lean_errorDescriptionWidget;
static lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22;
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lean_getErrorExplanationRaw_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__25;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37;
lean_object* l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(lean_object*);
lean_object* l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5;
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52;
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__26;
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11;
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__0;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3;
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14;
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__26;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11;
lean_object* l_Lean_Elab_addCompletionInfo___at___Lean_Elab_Term_addDotCompletionInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__23;
lean_object* l_Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0;
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10;
lean_object* l_Lean_Elab_pushInfoLeaf___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
extern lean_object* l_Lean_errorExplanationExt;
static lean_object* _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("errorDescriptionWidget", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2;
x_3 = l_Lean_errorDescriptionWidget;
x_4 = l_Lean_Widget_addBuiltinModule(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwNamedErrorMacro", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwNamedErrorAtMacro", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedErrorMacro", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedErrorAtMacro", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedWarningMacro", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedWarningAtMacro", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.logNamedWarningAt", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedWarningAt", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termM!_", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("m!", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.logNamedWarning", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedWarning", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.logNamedErrorAt", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedErrorAt", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.logNamedError", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("logNamedError", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.throwNamedErrorAt", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwNamedErrorAt", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.throwNamedError", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwNamedError", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59;
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
x_4 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_matchesNull(x_19, x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
lean_dec(x_1);
x_28 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
lean_inc(x_27);
x_29 = l_Lean_Syntax_isOfKind(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 5);
lean_inc(x_32);
lean_dec(x_2);
x_33 = l_Lean_SourceInfo_fromRef(x_32, x_29);
lean_dec(x_32);
x_34 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_35 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19;
x_36 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
x_37 = l_Lean_addMacroScope(x_30, x_36, x_31);
x_38 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23;
lean_inc(x_33);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
x_40 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_41 = l_Lean_Syntax_getId(x_25);
lean_dec(x_25);
x_42 = l_Lean_instQuoteNameMkStr1___private__1(x_41);
lean_inc(x_33);
x_43 = l_Lean_Syntax_node3(x_33, x_40, x_23, x_42, x_27);
x_44 = l_Lean_Syntax_node2(x_33, x_34, x_39, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 5);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Lean_SourceInfo_fromRef(x_48, x_13);
lean_dec(x_48);
x_50 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_51 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19;
x_52 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
x_53 = l_Lean_addMacroScope(x_46, x_52, x_47);
x_54 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23;
lean_inc(x_49);
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_54);
x_56 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_57 = l_Lean_Syntax_getId(x_25);
lean_dec(x_25);
x_58 = l_Lean_instQuoteNameMkStr1___private__1(x_57);
x_59 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
x_60 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
lean_inc(x_49);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_60);
lean_inc(x_49);
x_62 = l_Lean_Syntax_node2(x_49, x_59, x_61, x_27);
lean_inc(x_49);
x_63 = l_Lean_Syntax_node3(x_49, x_56, x_23, x_58, x_62);
x_64 = l_Lean_Syntax_node2(x_49, x_50, x_55, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_unsigned_to_nat(2u);
x_68 = l_Lean_Syntax_getArg(x_1, x_67);
x_69 = l_Lean_Syntax_matchesNull(x_68, x_66);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_2);
lean_dec(x_1);
x_70 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_unsigned_to_nat(1u);
x_72 = l_Lean_Syntax_getArg(x_1, x_71);
x_73 = lean_unsigned_to_nat(3u);
x_74 = l_Lean_Syntax_getArg(x_1, x_73);
lean_dec(x_1);
x_75 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
lean_inc(x_74);
x_76 = l_Lean_Syntax_isOfKind(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 5);
lean_inc(x_79);
lean_dec(x_2);
x_80 = l_Lean_SourceInfo_fromRef(x_79, x_76);
lean_dec(x_79);
x_81 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_82 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_83 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
x_84 = l_Lean_addMacroScope(x_77, x_83, x_78);
x_85 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34;
lean_inc(x_80);
x_86 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_84);
lean_ctor_set(x_86, 3, x_85);
x_87 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_88 = l_Lean_Syntax_getId(x_72);
lean_dec(x_72);
x_89 = l_Lean_instQuoteNameMkStr1___private__1(x_88);
lean_inc(x_80);
x_90 = l_Lean_Syntax_node2(x_80, x_87, x_89, x_74);
x_91 = l_Lean_Syntax_node2(x_80, x_81, x_86, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_3);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_93 = lean_ctor_get(x_2, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_2, 5);
lean_inc(x_95);
lean_dec(x_2);
x_96 = l_Lean_SourceInfo_fromRef(x_95, x_11);
lean_dec(x_95);
x_97 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_98 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30;
x_99 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
x_100 = l_Lean_addMacroScope(x_93, x_99, x_94);
x_101 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34;
lean_inc(x_96);
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_102, 2, x_100);
lean_ctor_set(x_102, 3, x_101);
x_103 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_104 = l_Lean_Syntax_getId(x_72);
lean_dec(x_72);
x_105 = l_Lean_instQuoteNameMkStr1___private__1(x_104);
x_106 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
x_107 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
lean_inc(x_96);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_96);
lean_ctor_set(x_108, 1, x_107);
lean_inc(x_96);
x_109 = l_Lean_Syntax_node2(x_96, x_106, x_108, x_74);
lean_inc(x_96);
x_110 = l_Lean_Syntax_node2(x_96, x_103, x_105, x_109);
x_111 = l_Lean_Syntax_node2(x_96, x_97, x_102, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_3);
return x_112;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_unsigned_to_nat(3u);
x_115 = l_Lean_Syntax_getArg(x_1, x_114);
x_116 = l_Lean_Syntax_matchesNull(x_115, x_113);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_2);
lean_dec(x_1);
x_117 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_118 = lean_unsigned_to_nat(1u);
x_119 = l_Lean_Syntax_getArg(x_1, x_118);
x_120 = lean_unsigned_to_nat(2u);
x_121 = l_Lean_Syntax_getArg(x_1, x_120);
x_122 = lean_unsigned_to_nat(4u);
x_123 = l_Lean_Syntax_getArg(x_1, x_122);
lean_dec(x_1);
x_124 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
lean_inc(x_123);
x_125 = l_Lean_Syntax_isOfKind(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_2, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_2, 5);
lean_inc(x_128);
lean_dec(x_2);
x_129 = l_Lean_SourceInfo_fromRef(x_128, x_125);
lean_dec(x_128);
x_130 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_131 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
x_132 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
x_133 = l_Lean_addMacroScope(x_126, x_132, x_127);
x_134 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40;
lean_inc(x_129);
x_135 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_133);
lean_ctor_set(x_135, 3, x_134);
x_136 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_137 = l_Lean_Syntax_getId(x_121);
lean_dec(x_121);
x_138 = l_Lean_instQuoteNameMkStr1___private__1(x_137);
lean_inc(x_129);
x_139 = l_Lean_Syntax_node3(x_129, x_136, x_119, x_138, x_123);
x_140 = l_Lean_Syntax_node2(x_129, x_130, x_135, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_3);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_142 = lean_ctor_get(x_2, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_2, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_2, 5);
lean_inc(x_144);
lean_dec(x_2);
x_145 = l_Lean_SourceInfo_fromRef(x_144, x_9);
lean_dec(x_144);
x_146 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_147 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
x_148 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
x_149 = l_Lean_addMacroScope(x_142, x_148, x_143);
x_150 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40;
lean_inc(x_145);
x_151 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_147);
lean_ctor_set(x_151, 2, x_149);
lean_ctor_set(x_151, 3, x_150);
x_152 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_153 = l_Lean_Syntax_getId(x_121);
lean_dec(x_121);
x_154 = l_Lean_instQuoteNameMkStr1___private__1(x_153);
x_155 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
x_156 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
lean_inc(x_145);
x_157 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_157, 0, x_145);
lean_ctor_set(x_157, 1, x_156);
lean_inc(x_145);
x_158 = l_Lean_Syntax_node2(x_145, x_155, x_157, x_123);
lean_inc(x_145);
x_159 = l_Lean_Syntax_node3(x_145, x_152, x_119, x_154, x_158);
x_160 = l_Lean_Syntax_node2(x_145, x_146, x_151, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_3);
return x_161;
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_unsigned_to_nat(2u);
x_164 = l_Lean_Syntax_getArg(x_1, x_163);
x_165 = l_Lean_Syntax_matchesNull(x_164, x_162);
if (x_165 == 0)
{
lean_object* x_166; 
lean_dec(x_2);
lean_dec(x_1);
x_166 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_167 = lean_unsigned_to_nat(1u);
x_168 = l_Lean_Syntax_getArg(x_1, x_167);
x_169 = lean_unsigned_to_nat(3u);
x_170 = l_Lean_Syntax_getArg(x_1, x_169);
lean_dec(x_1);
x_171 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
lean_inc(x_170);
x_172 = l_Lean_Syntax_isOfKind(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_173 = lean_ctor_get(x_2, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_2, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_2, 5);
lean_inc(x_175);
lean_dec(x_2);
x_176 = l_Lean_SourceInfo_fromRef(x_175, x_172);
lean_dec(x_175);
x_177 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_178 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
x_179 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44;
x_180 = l_Lean_addMacroScope(x_173, x_179, x_174);
x_181 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46;
lean_inc(x_176);
x_182 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_182, 0, x_176);
lean_ctor_set(x_182, 1, x_178);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set(x_182, 3, x_181);
x_183 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_184 = l_Lean_Syntax_getId(x_168);
lean_dec(x_168);
x_185 = l_Lean_instQuoteNameMkStr1___private__1(x_184);
lean_inc(x_176);
x_186 = l_Lean_Syntax_node2(x_176, x_183, x_185, x_170);
x_187 = l_Lean_Syntax_node2(x_176, x_177, x_182, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_3);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_189 = lean_ctor_get(x_2, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_2, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_2, 5);
lean_inc(x_191);
lean_dec(x_2);
x_192 = l_Lean_SourceInfo_fromRef(x_191, x_7);
lean_dec(x_191);
x_193 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_194 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
x_195 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44;
x_196 = l_Lean_addMacroScope(x_189, x_195, x_190);
x_197 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46;
lean_inc(x_192);
x_198 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_198, 0, x_192);
lean_ctor_set(x_198, 1, x_194);
lean_ctor_set(x_198, 2, x_196);
lean_ctor_set(x_198, 3, x_197);
x_199 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_200 = l_Lean_Syntax_getId(x_168);
lean_dec(x_168);
x_201 = l_Lean_instQuoteNameMkStr1___private__1(x_200);
x_202 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
x_203 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
lean_inc(x_192);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_192);
lean_ctor_set(x_204, 1, x_203);
lean_inc(x_192);
x_205 = l_Lean_Syntax_node2(x_192, x_202, x_204, x_170);
lean_inc(x_192);
x_206 = l_Lean_Syntax_node2(x_192, x_199, x_201, x_205);
x_207 = l_Lean_Syntax_node2(x_192, x_193, x_198, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_3);
return x_208;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_209 = lean_unsigned_to_nat(0u);
x_210 = lean_unsigned_to_nat(3u);
x_211 = l_Lean_Syntax_getArg(x_1, x_210);
x_212 = l_Lean_Syntax_matchesNull(x_211, x_209);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_2);
lean_dec(x_1);
x_213 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_214 = lean_unsigned_to_nat(1u);
x_215 = l_Lean_Syntax_getArg(x_1, x_214);
x_216 = lean_unsigned_to_nat(2u);
x_217 = l_Lean_Syntax_getArg(x_1, x_216);
x_218 = lean_unsigned_to_nat(4u);
x_219 = l_Lean_Syntax_getArg(x_1, x_218);
lean_dec(x_1);
x_220 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
lean_inc(x_219);
x_221 = l_Lean_Syntax_isOfKind(x_219, x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_222 = lean_ctor_get(x_2, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_2, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_2, 5);
lean_inc(x_224);
lean_dec(x_2);
x_225 = l_Lean_SourceInfo_fromRef(x_224, x_221);
lean_dec(x_224);
x_226 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_227 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
x_228 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
x_229 = l_Lean_addMacroScope(x_222, x_228, x_223);
x_230 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52;
lean_inc(x_225);
x_231 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_231, 0, x_225);
lean_ctor_set(x_231, 1, x_227);
lean_ctor_set(x_231, 2, x_229);
lean_ctor_set(x_231, 3, x_230);
x_232 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_233 = l_Lean_Syntax_getId(x_217);
lean_dec(x_217);
x_234 = l_Lean_instQuoteNameMkStr1___private__1(x_233);
lean_inc(x_225);
x_235 = l_Lean_Syntax_node3(x_225, x_232, x_215, x_234, x_219);
x_236 = l_Lean_Syntax_node2(x_225, x_226, x_231, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_3);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_238 = lean_ctor_get(x_2, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_2, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_2, 5);
lean_inc(x_240);
lean_dec(x_2);
x_241 = l_Lean_SourceInfo_fromRef(x_240, x_5);
lean_dec(x_240);
x_242 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_243 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
x_244 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
x_245 = l_Lean_addMacroScope(x_238, x_244, x_239);
x_246 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52;
lean_inc(x_241);
x_247 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_243);
lean_ctor_set(x_247, 2, x_245);
lean_ctor_set(x_247, 3, x_246);
x_248 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_249 = l_Lean_Syntax_getId(x_217);
lean_dec(x_217);
x_250 = l_Lean_instQuoteNameMkStr1___private__1(x_249);
x_251 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
x_252 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
lean_inc(x_241);
x_253 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_253, 0, x_241);
lean_ctor_set(x_253, 1, x_252);
lean_inc(x_241);
x_254 = l_Lean_Syntax_node2(x_241, x_251, x_253, x_219);
lean_inc(x_241);
x_255 = l_Lean_Syntax_node3(x_241, x_248, x_215, x_250, x_254);
x_256 = l_Lean_Syntax_node2(x_241, x_242, x_247, x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_3);
return x_257;
}
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_258 = lean_unsigned_to_nat(0u);
x_259 = lean_unsigned_to_nat(1u);
x_260 = l_Lean_Syntax_getArg(x_1, x_259);
x_261 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54;
lean_inc(x_260);
x_262 = l_Lean_Syntax_isOfKind(x_260, x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_unsigned_to_nat(2u);
x_264 = l_Lean_Syntax_getArg(x_1, x_263);
x_265 = l_Lean_Syntax_matchesNull(x_264, x_258);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec(x_260);
lean_dec(x_2);
lean_dec(x_1);
x_266 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_267 = lean_ctor_get(x_2, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_2, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_2, 5);
lean_inc(x_269);
lean_dec(x_2);
x_270 = lean_unsigned_to_nat(3u);
x_271 = l_Lean_Syntax_getArg(x_1, x_270);
lean_dec(x_1);
x_272 = l_Lean_SourceInfo_fromRef(x_269, x_262);
lean_dec(x_269);
x_273 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_274 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
x_275 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
x_276 = l_Lean_addMacroScope(x_267, x_275, x_268);
x_277 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60;
lean_inc(x_272);
x_278 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_278, 0, x_272);
lean_ctor_set(x_278, 1, x_274);
lean_ctor_set(x_278, 2, x_276);
lean_ctor_set(x_278, 3, x_277);
x_279 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_280 = l_Lean_Syntax_getId(x_260);
lean_dec(x_260);
x_281 = l_Lean_instQuoteNameMkStr1___private__1(x_280);
lean_inc(x_272);
x_282 = l_Lean_Syntax_node2(x_272, x_279, x_281, x_271);
x_283 = l_Lean_Syntax_node2(x_272, x_273, x_278, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_3);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_unsigned_to_nat(2u);
x_286 = l_Lean_Syntax_getArg(x_1, x_285);
x_287 = l_Lean_Syntax_matchesNull(x_286, x_258);
if (x_287 == 0)
{
lean_object* x_288; 
lean_dec(x_260);
lean_dec(x_2);
lean_dec(x_1);
x_288 = l_Lean_Macro_throwUnsupported___redArg(x_3);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_289 = lean_unsigned_to_nat(3u);
x_290 = l_Lean_Syntax_getArg(x_1, x_289);
lean_dec(x_1);
x_291 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
lean_inc(x_290);
x_292 = l_Lean_Syntax_isOfKind(x_290, x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_293 = lean_ctor_get(x_2, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_2, 2);
lean_inc(x_294);
x_295 = lean_ctor_get(x_2, 5);
lean_inc(x_295);
lean_dec(x_2);
x_296 = l_Lean_SourceInfo_fromRef(x_295, x_292);
lean_dec(x_295);
x_297 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_298 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
x_299 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
x_300 = l_Lean_addMacroScope(x_293, x_299, x_294);
x_301 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60;
lean_inc(x_296);
x_302 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_302, 0, x_296);
lean_ctor_set(x_302, 1, x_298);
lean_ctor_set(x_302, 2, x_300);
lean_ctor_set(x_302, 3, x_301);
x_303 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_304 = l_Lean_Syntax_getId(x_260);
lean_dec(x_260);
x_305 = l_Lean_instQuoteNameMkStr1___private__1(x_304);
lean_inc(x_296);
x_306 = l_Lean_Syntax_node2(x_296, x_303, x_305, x_290);
x_307 = l_Lean_Syntax_node2(x_296, x_297, x_302, x_306);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_3);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_309 = lean_ctor_get(x_2, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_2, 2);
lean_inc(x_310);
x_311 = lean_ctor_get(x_2, 5);
lean_inc(x_311);
lean_dec(x_2);
x_312 = lean_box(0);
x_313 = lean_unbox(x_312);
x_314 = l_Lean_SourceInfo_fromRef(x_311, x_313);
lean_dec(x_311);
x_315 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
x_316 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
x_317 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
x_318 = l_Lean_addMacroScope(x_309, x_317, x_310);
x_319 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60;
lean_inc(x_314);
x_320 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_320, 0, x_314);
lean_ctor_set(x_320, 1, x_316);
lean_ctor_set(x_320, 2, x_318);
lean_ctor_set(x_320, 3, x_319);
x_321 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
x_322 = l_Lean_Syntax_getId(x_260);
lean_dec(x_260);
x_323 = l_Lean_instQuoteNameMkStr1___private__1(x_322);
x_324 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
x_325 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
lean_inc(x_314);
x_326 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_326, 0, x_314);
lean_ctor_set(x_326, 1, x_325);
lean_inc(x_314);
x_327 = l_Lean_Syntax_node2(x_314, x_324, x_326, x_290);
lean_inc(x_314);
x_328 = l_Lean_Syntax_node2(x_314, x_321, x_323, x_327);
x_329 = l_Lean_Syntax_node2(x_314, x_315, x_320, x_328);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_3);
return x_330;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_array_get_size(x_9);
x_11 = l_Lean_Name_hash___override(x_5);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_9, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DTreeMap_Internal_Lemmas_0__Std_DTreeMap_Internal_Impl_modifyMap_spec__0___redArg(x_5, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 2, x_23);
x_28 = lean_array_uset(x_9, x_22, x_27);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_nat_mul(x_26, x_29);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_nat_div(x_30, x_31);
lean_dec(x_30);
x_33 = lean_array_get_size(x_28);
x_34 = lean_nat_dec_le(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DTreeMap_Internal_Lemmas_0__Std_DTreeMap_Internal_Impl_modifyMap_spec__1___redArg(x_28);
lean_ctor_set(x_2, 1, x_35);
lean_ctor_set(x_2, 0, x_26);
x_1 = x_4;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_26);
x_1 = x_4;
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_array_uset(x_9, x_22, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Std_Data_DTreeMap_Internal_Lemmas_0__Std_DTreeMap_Internal_Impl_modifyMap_spec__4___redArg(x_5, x_6, x_23);
x_41 = lean_array_uset(x_39, x_22, x_40);
lean_ctor_set(x_2, 1, x_41);
x_1 = x_4;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; uint8_t x_59; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_45 = lean_array_get_size(x_44);
x_46 = l_Lean_Name_hash___override(x_5);
x_47 = 32;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = 16;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_xor(x_49, x_51);
x_53 = lean_uint64_to_usize(x_52);
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = 1;
x_56 = lean_usize_sub(x_54, x_55);
x_57 = lean_usize_land(x_53, x_56);
x_58 = lean_array_uget(x_44, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Std_Data_DTreeMap_Internal_Lemmas_0__Std_DTreeMap_Internal_Impl_modifyMap_spec__0___redArg(x_5, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_43, x_60);
lean_dec(x_43);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_5);
lean_ctor_set(x_62, 1, x_6);
lean_ctor_set(x_62, 2, x_58);
x_63 = lean_array_uset(x_44, x_57, x_62);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_nat_mul(x_61, x_64);
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_div(x_65, x_66);
lean_dec(x_65);
x_68 = lean_array_get_size(x_63);
x_69 = lean_nat_dec_le(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Std_Data_DTreeMap_Internal_Lemmas_0__Std_DTreeMap_Internal_Impl_modifyMap_spec__1___redArg(x_63);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_70);
x_1 = x_4;
x_2 = x_71;
goto _start;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_63);
x_1 = x_4;
x_2 = x_73;
goto _start;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_box(0);
x_76 = lean_array_uset(x_44, x_57, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Std_Data_DTreeMap_Internal_Lemmas_0__Std_DTreeMap_Internal_Impl_modifyMap_spec__4___redArg(x_5, x_6, x_58);
x_78 = lean_array_uset(x_76, x_57, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_43);
lean_ctor_set(x_79, 1, x_78);
x_1 = x_4;
x_2 = x_79;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at_____private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___redArg(x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Exception", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Log", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14;
x_2 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13;
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
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__25;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21;
x_2 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__26;
x_3 = l_List_forIn_x27_loop___at_____private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at_____private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1_spec__1___redArg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("There is no explanation associated with the name `", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`. Add an explanation of this error to the `Lean.ErrorExplanations` module.", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The error name `", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` was removed in Lean version ", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" and should not be used.", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The constant `", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has not been imported", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Add `import ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` to this file's header to use this macro", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_227; uint8_t x_228; 
x_227 = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; uint64_t x_238; uint64_t x_239; size_t x_240; size_t x_241; size_t x_242; size_t x_243; size_t x_244; lean_object* x_245; lean_object* x_246; 
x_229 = lean_ctor_get(x_227, 1);
x_230 = lean_ctor_get(x_227, 0);
lean_dec(x_230);
lean_inc(x_1);
x_231 = l_Lean_Syntax_getKind(x_1);
x_232 = lean_array_get_size(x_229);
x_233 = l_Lean_Name_hash___override(x_231);
x_234 = 32;
x_235 = lean_uint64_shift_right(x_233, x_234);
x_236 = lean_uint64_xor(x_233, x_235);
x_237 = 16;
x_238 = lean_uint64_shift_right(x_236, x_237);
x_239 = lean_uint64_xor(x_236, x_238);
x_240 = lean_uint64_to_usize(x_239);
x_241 = lean_usize_of_nat(x_232);
lean_dec(x_232);
x_242 = 1;
x_243 = lean_usize_sub(x_241, x_242);
x_244 = lean_usize_land(x_240, x_243);
x_245 = lean_array_uget(x_229, x_244);
lean_dec(x_229);
x_246 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_231, x_245);
lean_dec(x_245);
lean_dec(x_231);
if (lean_obj_tag(x_246) == 0)
{
lean_free_object(x_227);
x_215 = x_3;
x_216 = x_4;
x_217 = x_5;
x_218 = x_6;
x_219 = x_7;
x_220 = x_8;
x_221 = x_9;
goto block_226;
}
else
{
lean_object* x_247; uint8_t x_248; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec(x_246);
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_247, 0);
x_250 = lean_ctor_get(x_247, 1);
x_251 = lean_st_ref_get(x_8, x_9);
x_252 = !lean_is_exclusive(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_258; 
x_253 = lean_ctor_get(x_251, 0);
x_254 = lean_ctor_get(x_251, 1);
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_box(1);
x_257 = lean_unbox(x_256);
lean_inc(x_250);
x_258 = l_Lean_Environment_contains(x_255, x_250, x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_dec(x_2);
lean_dec(x_1);
x_259 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11;
x_260 = l_Lean_MessageData_ofName(x_250);
lean_ctor_set_tag(x_251, 7);
lean_ctor_set(x_251, 1, x_260);
lean_ctor_set(x_251, 0, x_259);
x_261 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13;
lean_ctor_set_tag(x_247, 7);
lean_ctor_set(x_247, 1, x_261);
lean_ctor_set(x_247, 0, x_251);
x_262 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15;
x_263 = l_Lean_MessageData_ofName(x_249);
lean_ctor_set_tag(x_227, 7);
lean_ctor_set(x_227, 1, x_263);
lean_ctor_set(x_227, 0, x_262);
x_264 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17;
x_265 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_265, 0, x_227);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Lean_MessageData_hint_x27(x_265);
x_267 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_267, 0, x_247);
lean_ctor_set(x_267, 1, x_266);
x_268 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_267, x_3, x_4, x_5, x_6, x_7, x_8, x_254);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
return x_268;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_268);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
else
{
lean_free_object(x_251);
lean_free_object(x_247);
lean_dec(x_250);
lean_dec(x_249);
lean_free_object(x_227);
x_215 = x_3;
x_216 = x_4;
x_217 = x_5;
x_218 = x_6;
x_219 = x_7;
x_220 = x_8;
x_221 = x_254;
goto block_226;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; uint8_t x_278; 
x_273 = lean_ctor_get(x_251, 0);
x_274 = lean_ctor_get(x_251, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_251);
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_box(1);
x_277 = lean_unbox(x_276);
lean_inc(x_250);
x_278 = l_Lean_Environment_contains(x_275, x_250, x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_2);
lean_dec(x_1);
x_279 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11;
x_280 = l_Lean_MessageData_ofName(x_250);
x_281 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_282 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13;
lean_ctor_set_tag(x_247, 7);
lean_ctor_set(x_247, 1, x_282);
lean_ctor_set(x_247, 0, x_281);
x_283 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15;
x_284 = l_Lean_MessageData_ofName(x_249);
lean_ctor_set_tag(x_227, 7);
lean_ctor_set(x_227, 1, x_284);
lean_ctor_set(x_227, 0, x_283);
x_285 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17;
x_286 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_286, 0, x_227);
lean_ctor_set(x_286, 1, x_285);
x_287 = l_Lean_MessageData_hint_x27(x_286);
x_288 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_288, 0, x_247);
lean_ctor_set(x_288, 1, x_287);
x_289 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_288, x_3, x_4, x_5, x_6, x_7, x_8, x_274);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_292 = x_289;
} else {
 lean_dec_ref(x_289);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
else
{
lean_free_object(x_247);
lean_dec(x_250);
lean_dec(x_249);
lean_free_object(x_227);
x_215 = x_3;
x_216 = x_4;
x_217 = x_5;
x_218 = x_6;
x_219 = x_7;
x_220 = x_8;
x_221 = x_274;
goto block_226;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_303; 
x_294 = lean_ctor_get(x_247, 0);
x_295 = lean_ctor_get(x_247, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_247);
x_296 = lean_st_ref_get(x_8, x_9);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_299 = x_296;
} else {
 lean_dec_ref(x_296);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_297, 0);
lean_inc(x_300);
lean_dec(x_297);
x_301 = lean_box(1);
x_302 = lean_unbox(x_301);
lean_inc(x_295);
x_303 = l_Lean_Environment_contains(x_300, x_295, x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_2);
lean_dec(x_1);
x_304 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11;
x_305 = l_Lean_MessageData_ofName(x_295);
if (lean_is_scalar(x_299)) {
 x_306 = lean_alloc_ctor(7, 2, 0);
} else {
 x_306 = x_299;
 lean_ctor_set_tag(x_306, 7);
}
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13;
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15;
x_310 = l_Lean_MessageData_ofName(x_294);
lean_ctor_set_tag(x_227, 7);
lean_ctor_set(x_227, 1, x_310);
lean_ctor_set(x_227, 0, x_309);
x_311 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17;
x_312 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_312, 0, x_227);
lean_ctor_set(x_312, 1, x_311);
x_313 = l_Lean_MessageData_hint_x27(x_312);
x_314 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_314, 0, x_308);
lean_ctor_set(x_314, 1, x_313);
x_315 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_314, x_3, x_4, x_5, x_6, x_7, x_8, x_298);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_318 = x_315;
} else {
 lean_dec_ref(x_315);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
else
{
lean_dec(x_299);
lean_dec(x_295);
lean_dec(x_294);
lean_free_object(x_227);
x_215 = x_3;
x_216 = x_4;
x_217 = x_5;
x_218 = x_6;
x_219 = x_7;
x_220 = x_8;
x_221 = x_298;
goto block_226;
}
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; uint64_t x_323; uint64_t x_324; uint64_t x_325; uint64_t x_326; uint64_t x_327; uint64_t x_328; uint64_t x_329; size_t x_330; size_t x_331; size_t x_332; size_t x_333; size_t x_334; lean_object* x_335; lean_object* x_336; 
x_320 = lean_ctor_get(x_227, 1);
lean_inc(x_320);
lean_dec(x_227);
lean_inc(x_1);
x_321 = l_Lean_Syntax_getKind(x_1);
x_322 = lean_array_get_size(x_320);
x_323 = l_Lean_Name_hash___override(x_321);
x_324 = 32;
x_325 = lean_uint64_shift_right(x_323, x_324);
x_326 = lean_uint64_xor(x_323, x_325);
x_327 = 16;
x_328 = lean_uint64_shift_right(x_326, x_327);
x_329 = lean_uint64_xor(x_326, x_328);
x_330 = lean_uint64_to_usize(x_329);
x_331 = lean_usize_of_nat(x_322);
lean_dec(x_322);
x_332 = 1;
x_333 = lean_usize_sub(x_331, x_332);
x_334 = lean_usize_land(x_330, x_333);
x_335 = lean_array_uget(x_320, x_334);
lean_dec(x_320);
x_336 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Lemmas______macroRules__Std__DTreeMap__Internal__Impl__tacticSimp__to__model_x5b___x5dUsing____1_spec__0___redArg(x_321, x_335);
lean_dec(x_335);
lean_dec(x_321);
if (lean_obj_tag(x_336) == 0)
{
x_215 = x_3;
x_216 = x_4;
x_217 = x_5;
x_218 = x_6;
x_219 = x_7;
x_220 = x_8;
x_221 = x_9;
goto block_226;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; uint8_t x_348; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
lean_dec(x_336);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
x_341 = lean_st_ref_get(x_8, x_9);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_344 = x_341;
} else {
 lean_dec_ref(x_341);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
lean_dec(x_342);
x_346 = lean_box(1);
x_347 = lean_unbox(x_346);
lean_inc(x_339);
x_348 = l_Lean_Environment_contains(x_345, x_339, x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_2);
lean_dec(x_1);
x_349 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11;
x_350 = l_Lean_MessageData_ofName(x_339);
if (lean_is_scalar(x_344)) {
 x_351 = lean_alloc_ctor(7, 2, 0);
} else {
 x_351 = x_344;
 lean_ctor_set_tag(x_351, 7);
}
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13;
if (lean_is_scalar(x_340)) {
 x_353 = lean_alloc_ctor(7, 2, 0);
} else {
 x_353 = x_340;
 lean_ctor_set_tag(x_353, 7);
}
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_354 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15;
x_355 = l_Lean_MessageData_ofName(x_338);
x_356 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
x_357 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17;
x_358 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_359 = l_Lean_MessageData_hint_x27(x_358);
x_360 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_360, 0, x_353);
lean_ctor_set(x_360, 1, x_359);
x_361 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_360, x_3, x_4, x_5, x_6, x_7, x_8, x_343);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_364 = x_361;
} else {
 lean_dec_ref(x_361);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_363);
return x_365;
}
else
{
lean_dec(x_344);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
x_215 = x_3;
x_216 = x_4;
x_217 = x_5;
x_218 = x_6;
x_219 = x_7;
x_220 = x_8;
x_221 = x_343;
goto block_226;
}
}
}
block_27:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro), 3, 1);
lean_closure_set(x_18, 0, x_1);
lean_inc(x_15);
lean_inc(x_11);
x_19 = l_Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0___redArg(x_18, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_elabTerm(x_20, x_2, x_10, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
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
block_167:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = l_Lean_Syntax_getNumArgs(x_37);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_sub(x_38, x_39);
lean_dec(x_38);
x_41 = l_Lean_Syntax_getArg(x_37, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Elab_addCompletionInfo___at___Lean_Elab_Term_addDotCompletionInfo_spec__0(x_42, x_28, x_30, x_36, x_32, x_35, x_29, x_31);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = l_Lean_Syntax_getId(x_34);
x_48 = lean_erase_macro_scopes(x_47);
lean_inc(x_48);
lean_inc(x_34);
lean_ctor_set(x_43, 1, x_48);
lean_ctor_set(x_43, 0, x_34);
x_49 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_49, 0, x_43);
x_50 = l_Lean_Elab_pushInfoLeaf___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__0(x_49, x_28, x_30, x_36, x_32, x_35, x_29, x_45);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = lean_st_ref_get(x_29, x_52);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_getErrorExplanationRaw_x3f(x_58, x_48);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1;
x_61 = l_Lean_MessageData_ofName(x_48);
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_61);
lean_ctor_set(x_54, 0, x_60);
x_62 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3;
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_62);
lean_ctor_set(x_50, 0, x_54);
lean_inc(x_35);
x_63 = l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(x_34, x_50, x_28, x_30, x_36, x_32, x_35, x_29, x_57);
lean_dec(x_34);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_64;
goto block_27;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get(x_66, 2);
lean_inc(x_67);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_free_object(x_54);
lean_free_object(x_50);
lean_dec(x_48);
lean_dec(x_34);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_57;
goto block_27;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5;
x_70 = l_Lean_MessageData_ofName(x_48);
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_70);
lean_ctor_set(x_54, 0, x_69);
x_71 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7;
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_71);
lean_ctor_set(x_50, 0, x_54);
x_72 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_50);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_35);
x_76 = l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(x_34, x_75, x_36, x_32, x_35, x_29, x_57);
lean_dec(x_34);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_77;
goto block_27;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_54, 0);
x_79 = lean_ctor_get(x_54, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_54);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_getErrorExplanationRaw_x3f(x_80, x_48);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1;
x_83 = l_Lean_MessageData_ofName(x_48);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3;
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_85);
lean_ctor_set(x_50, 0, x_84);
lean_inc(x_35);
x_86 = l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(x_34, x_50, x_28, x_30, x_36, x_32, x_35, x_29, x_79);
lean_dec(x_34);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_87;
goto block_27;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
lean_dec(x_81);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get(x_89, 2);
lean_inc(x_90);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_free_object(x_50);
lean_dec(x_48);
lean_dec(x_34);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_79;
goto block_27;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5;
x_93 = l_Lean_MessageData_ofName(x_48);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7;
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_95);
lean_ctor_set(x_50, 0, x_94);
x_96 = l_Lean_stringToMessageData(x_91);
lean_dec(x_91);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_50);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_inc(x_35);
x_100 = l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(x_34, x_99, x_36, x_32, x_35, x_29, x_79);
lean_dec(x_34);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_101;
goto block_27;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_50, 1);
lean_inc(x_102);
lean_dec(x_50);
x_103 = lean_st_ref_get(x_29, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
lean_dec(x_104);
x_108 = l_Lean_getErrorExplanationRaw_x3f(x_107, x_48);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1;
x_110 = l_Lean_MessageData_ofName(x_48);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(7, 2, 0);
} else {
 x_111 = x_106;
 lean_ctor_set_tag(x_111, 7);
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
lean_inc(x_35);
x_114 = l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(x_34, x_113, x_28, x_30, x_36, x_32, x_35, x_29, x_105);
lean_dec(x_34);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_115;
goto block_27;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_108, 0);
lean_inc(x_116);
lean_dec(x_108);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get(x_117, 2);
lean_inc(x_118);
lean_dec(x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_dec(x_106);
lean_dec(x_48);
lean_dec(x_34);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_105;
goto block_27;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
x_120 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5;
x_121 = l_Lean_MessageData_ofName(x_48);
if (lean_is_scalar(x_106)) {
 x_122 = lean_alloc_ctor(7, 2, 0);
} else {
 x_122 = x_106;
 lean_ctor_set_tag(x_122, 7);
}
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7;
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_stringToMessageData(x_119);
lean_dec(x_119);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_inc(x_35);
x_129 = l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(x_34, x_128, x_36, x_32, x_35, x_29, x_105);
lean_dec(x_34);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_130;
goto block_27;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_131 = lean_ctor_get(x_43, 1);
lean_inc(x_131);
lean_dec(x_43);
x_132 = l_Lean_Syntax_getId(x_34);
x_133 = lean_erase_macro_scopes(x_132);
lean_inc(x_133);
lean_inc(x_34);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_34);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = l_Lean_Elab_pushInfoLeaf___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__0(x_135, x_28, x_30, x_36, x_32, x_35, x_29, x_131);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_st_ref_get(x_29, x_137);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
lean_dec(x_140);
x_144 = l_Lean_getErrorExplanationRaw_x3f(x_143, x_133);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1;
x_146 = l_Lean_MessageData_ofName(x_133);
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(7, 2, 0);
} else {
 x_147 = x_142;
 lean_ctor_set_tag(x_147, 7);
}
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3;
if (lean_is_scalar(x_138)) {
 x_149 = lean_alloc_ctor(7, 2, 0);
} else {
 x_149 = x_138;
 lean_ctor_set_tag(x_149, 7);
}
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
lean_inc(x_35);
x_150 = l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(x_34, x_149, x_28, x_30, x_36, x_32, x_35, x_29, x_141);
lean_dec(x_34);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_151;
goto block_27;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_144, 0);
lean_inc(x_152);
lean_dec(x_144);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_ctor_get(x_153, 2);
lean_inc(x_154);
lean_dec(x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_dec(x_142);
lean_dec(x_138);
lean_dec(x_133);
lean_dec(x_34);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_141;
goto block_27;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec(x_154);
x_156 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5;
x_157 = l_Lean_MessageData_ofName(x_133);
if (lean_is_scalar(x_142)) {
 x_158 = lean_alloc_ctor(7, 2, 0);
} else {
 x_158 = x_142;
 lean_ctor_set_tag(x_158, 7);
}
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7;
if (lean_is_scalar(x_138)) {
 x_160 = lean_alloc_ctor(7, 2, 0);
} else {
 x_160 = x_138;
 lean_ctor_set_tag(x_160, 7);
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_stringToMessageData(x_155);
lean_dec(x_155);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9;
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
lean_inc(x_35);
x_165 = l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(x_34, x_164, x_36, x_32, x_35, x_29, x_141);
lean_dec(x_34);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_10 = x_33;
x_11 = x_28;
x_12 = x_30;
x_13 = x_36;
x_14 = x_32;
x_15 = x_35;
x_16 = x_29;
x_17 = x_166;
goto block_27;
}
}
}
}
block_189:
{
lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_177 = l_Lean_Syntax_getNumArgs(x_1);
x_178 = lean_nat_dec_eq(x_177, x_176);
x_179 = lean_box(1);
if (x_178 == 0)
{
uint8_t x_180; 
lean_dec(x_177);
x_180 = lean_unbox(x_179);
lean_inc(x_1);
x_28 = x_168;
x_29 = x_170;
x_30 = x_169;
x_31 = x_172;
x_32 = x_171;
x_33 = x_180;
x_34 = x_175;
x_35 = x_173;
x_36 = x_174;
x_37 = x_1;
goto block_167;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_181 = l_Lean_Syntax_getArgs(x_1);
x_182 = lean_unsigned_to_nat(0u);
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_nat_sub(x_177, x_183);
lean_dec(x_177);
x_185 = l_Array_toSubarray___redArg(x_181, x_182, x_184);
x_186 = l_Array_ofSubarray___redArg(x_185);
lean_dec(x_185);
lean_inc(x_1);
x_187 = l_Lean_Syntax_setArgs(x_1, x_186);
x_188 = lean_unbox(x_179);
x_28 = x_168;
x_29 = x_170;
x_30 = x_169;
x_31 = x_172;
x_32 = x_171;
x_33 = x_188;
x_34 = x_175;
x_35 = x_173;
x_36 = x_174;
x_37 = x_187;
goto block_167;
}
}
block_200:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_unsigned_to_nat(2u);
x_198 = l_Lean_Syntax_getArg(x_1, x_197);
x_199 = lean_unsigned_to_nat(5u);
x_168 = x_190;
x_169 = x_192;
x_170 = x_191;
x_171 = x_194;
x_172 = x_193;
x_173 = x_195;
x_174 = x_196;
x_175 = x_198;
x_176 = x_199;
goto block_189;
}
block_214:
{
if (x_208 == 0)
{
lean_object* x_209; uint8_t x_210; 
x_209 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
lean_inc(x_1);
x_210 = l_Lean_Syntax_isOfKind(x_1, x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_unsigned_to_nat(1u);
x_212 = l_Lean_Syntax_getArg(x_1, x_211);
x_213 = lean_unsigned_to_nat(4u);
x_168 = x_201;
x_169 = x_203;
x_170 = x_202;
x_171 = x_205;
x_172 = x_204;
x_173 = x_206;
x_174 = x_207;
x_175 = x_212;
x_176 = x_213;
goto block_189;
}
else
{
x_190 = x_201;
x_191 = x_202;
x_192 = x_203;
x_193 = x_204;
x_194 = x_205;
x_195 = x_206;
x_196 = x_207;
goto block_200;
}
}
else
{
x_190 = x_201;
x_191 = x_202;
x_192 = x_203;
x_193 = x_204;
x_194 = x_205;
x_195 = x_206;
x_196 = x_207;
goto block_200;
}
}
block_226:
{
lean_object* x_222; uint8_t x_223; 
x_222 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
lean_inc(x_1);
x_223 = l_Lean_Syntax_isOfKind(x_1, x_222);
if (x_223 == 0)
{
lean_object* x_224; uint8_t x_225; 
x_224 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
lean_inc(x_1);
x_225 = l_Lean_Syntax_isOfKind(x_1, x_224);
x_201 = x_215;
x_202 = x_220;
x_203 = x_216;
x_204 = x_221;
x_205 = x_218;
x_206 = x_219;
x_207 = x_217;
x_208 = x_225;
goto block_214;
}
else
{
x_201 = x_215;
x_202 = x_220;
x_203 = x_216;
x_204 = x_221;
x_205 = x_218;
x_206 = x_219;
x_207 = x_217;
x_208 = x_223;
goto block_214;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logWarningAt___at___Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_termElabAttribute;
return x_1;
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
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3;
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
x_3 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
x_4 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError), 9, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
lean_inc(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = lean_unbox(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_elabTerm(x_1, x_10, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_26; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_26 = l_Lean_Expr_hasSyntheticSorry(x_15);
if (x_26 == 0)
{
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_16;
goto block_25;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_27 = l_Lean_Elab_throwAbortTerm___at___Lean_Elab_Term_throwMVarError_spec__0___redArg(x_16);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
block_25:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Meta_evalExpr___redArg(x_2, x_15, x_23, x_17, x_18, x_19, x_20, x_21);
return x_24;
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = lean_array_uget(x_4, x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
lean_inc(x_8);
x_24 = l_Lean_logError___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__3(x_23, x_8, x_9, x_10);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_25;
goto block_16;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_nat_add(x_30, x_28);
x_32 = lean_nat_add(x_30, x_29);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_unbox(x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_35);
x_36 = lean_string_utf8_extract(x_3, x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 1, x_36);
lean_ctor_set(x_20, 0, x_34);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_26);
x_38 = l_Lean_MessageData_ofFormat(x_37);
lean_inc(x_8);
x_39 = l_Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0(x_20, x_38, x_8, x_9, x_10);
lean_dec(x_20);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_40;
goto block_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_nat_add(x_43, x_41);
x_45 = lean_nat_add(x_43, x_42);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_48);
x_49 = lean_string_utf8_extract(x_3, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_26);
x_52 = l_Lean_MessageData_ofFormat(x_51);
lean_inc(x_8);
x_53 = l_Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Command_runLinters_spec__0_spec__0(x_50, x_52, x_8, x_9, x_10);
lean_dec(x_50);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_2);
x_11 = x_2;
x_12 = x_54;
goto block_16;
}
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_6, x_13);
x_6 = x_14;
x_7 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = l_Lean_TSyntax_getDocString(x_1);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l_Lean_Syntax_getHeadInfo_x3f(x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
x_6 = x_23;
goto block_19;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_SourceInfo_getPos_x3f(x_24, x_26);
lean_dec(x_24);
x_6 = x_27;
goto block_19;
}
block_19:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
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
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0_spec__0(x_6, x_11, x_5, x_10, x_12, x_13, x_11, x_2, x_3, x_9);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected doc string", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_string_utf8_byte_size(x_8);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = lean_string_utf8_extract(x_8, x_10, x_13);
lean_dec(x_13);
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
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_byte_size(x_15);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_string_utf8_extract(x_15, x_16, x_19);
lean_dec(x_19);
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
x_22 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__1;
x_23 = l_Lean_MessageData_ofSyntax(x_6);
x_24 = l_Lean_indentD(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_1, x_27, x_2, x_3, x_4);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_errorExplanationExt;
return x_1;
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
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2;
x_2 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
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
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4;
x_2 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1;
x_3 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot add explanation: An error explanation already exists for `", 65, 65);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
x_2 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("To use this command, add `import Lean.ErrorExplanation` to the header of this file", 82, 82);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Metadata", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13;
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
x_3 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid name `", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`: Error explanation names must have two components", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The first component of an error explanation name identifies the package from which the error originates, and the second identifies the error itself.", 148, 148);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21;
x_2 = l_Lean_MessageData_note(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`: Error explanations cannot have inaccessible names. This error often occurs when an error explanation is generated using a macro.", 131, 131);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__23;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid name for error explanation: `", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__25;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_113; uint8_t x_114; 
x_113 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3;
lean_inc(x_1);
x_114 = l_Lean_Syntax_isOfKind(x_1, x_113);
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_2);
lean_dec(x_1);
x_115 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(x_4);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Lean_Syntax_getArg(x_1, x_116);
x_118 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5;
lean_inc(x_117);
x_119 = l_Lean_Syntax_isOfKind(x_117, x_118);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_117);
lean_dec(x_2);
lean_dec(x_1);
x_120 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(x_4);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_134; uint8_t x_135; 
x_121 = lean_unsigned_to_nat(2u);
x_122 = l_Lean_Syntax_getArg(x_1, x_121);
x_134 = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54;
lean_inc(x_122);
x_135 = l_Lean_Syntax_isOfKind(x_122, x_134);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_122);
lean_dec(x_117);
lean_dec(x_2);
lean_dec(x_1);
x_136 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__5___redArg(x_4);
return x_136;
}
else
{
lean_object* x_137; uint8_t x_138; 
x_137 = l_Lean_Elab_Command_getRef___redArg(x_2, x_4);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
x_141 = lean_st_ref_get(x_3, x_140);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_2);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_144 = lean_ctor_get(x_141, 0);
x_145 = lean_ctor_get(x_141, 1);
x_146 = lean_ctor_get(x_2, 6);
lean_dec(x_146);
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_unsigned_to_nat(1u);
x_408 = l_Lean_Syntax_getArg(x_1, x_148);
x_409 = lean_unsigned_to_nat(3u);
x_410 = l_Lean_Syntax_getArg(x_1, x_409);
lean_dec(x_1);
x_411 = l_Lean_replaceRef(x_408, x_139);
lean_dec(x_139);
lean_dec(x_408);
lean_ctor_set(x_2, 6, x_411);
x_412 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10;
x_413 = l_Lean_Environment_contains(x_147, x_412, x_135);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; 
lean_dec(x_410);
lean_free_object(x_141);
lean_free_object(x_137);
lean_dec(x_122);
lean_dec(x_117);
x_414 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12;
x_415 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_414, x_2, x_3, x_145);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15;
x_417 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed), 10, 2);
lean_closure_set(x_417, 0, x_410);
lean_closure_set(x_417, 1, x_416);
x_418 = l_Lean_Elab_Command_runTermElabM___redArg(x_417, x_2, x_3, x_145);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = l_Lean_Syntax_getId(x_122);
x_422 = l_Lean_Name_isAnonymous(x_421);
if (x_422 == 0)
{
uint8_t x_423; 
x_423 = l_Lean_Name_hasMacroScopes(x_421);
if (x_423 == 0)
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_Name_getNumParts(x_421);
x_425 = lean_nat_dec_eq(x_424, x_121);
lean_dec(x_424);
if (x_425 == 0)
{
if (x_135 == 0)
{
lean_free_object(x_141);
lean_free_object(x_137);
x_149 = x_421;
x_150 = x_419;
x_151 = x_2;
x_152 = x_3;
x_153 = x_420;
goto block_407;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_419);
lean_dec(x_117);
x_426 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
x_427 = l_Lean_MessageData_ofName(x_421);
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_427);
lean_ctor_set(x_141, 0, x_426);
x_428 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19;
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_428);
lean_ctor_set(x_137, 0, x_141);
x_429 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22;
x_430 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_430, 0, x_137);
lean_ctor_set(x_430, 1, x_429);
x_431 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_430, x_2, x_3, x_420);
lean_dec(x_122);
return x_431;
}
}
else
{
lean_free_object(x_141);
lean_free_object(x_137);
x_149 = x_421;
x_150 = x_419;
x_151 = x_2;
x_152 = x_3;
x_153 = x_420;
goto block_407;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_421);
lean_dec(x_419);
lean_dec(x_117);
x_432 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
lean_inc(x_122);
x_433 = l_Lean_MessageData_ofSyntax(x_122);
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_433);
lean_ctor_set(x_141, 0, x_432);
x_434 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__24;
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_434);
lean_ctor_set(x_137, 0, x_141);
x_435 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_137, x_2, x_3, x_420);
lean_dec(x_122);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_421);
lean_dec(x_419);
lean_dec(x_117);
x_436 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__26;
lean_inc(x_122);
x_437 = l_Lean_MessageData_ofSyntax(x_122);
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_437);
lean_ctor_set(x_141, 0, x_436);
x_438 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_438);
lean_ctor_set(x_137, 0, x_141);
x_439 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_137, x_2, x_3, x_420);
lean_dec(x_122);
return x_439;
}
}
else
{
uint8_t x_440; 
lean_dec(x_2);
lean_free_object(x_141);
lean_free_object(x_137);
lean_dec(x_122);
lean_dec(x_117);
x_440 = !lean_is_exclusive(x_418);
if (x_440 == 0)
{
return x_418;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_418, 0);
x_442 = lean_ctor_get(x_418, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_418);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
block_407:
{
lean_object* x_154; uint8_t x_155; 
lean_inc(x_151);
x_154 = l_Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(x_117, x_151, x_152, x_153);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_154, 1);
x_157 = lean_ctor_get(x_154, 0);
lean_dec(x_157);
lean_inc(x_151);
x_158 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(x_117, x_151, x_152, x_156);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_st_ref_get(x_152, x_160);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get_uint8(x_167, sizeof(void*)*3);
lean_dec(x_167);
x_169 = lean_box(0);
x_170 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_169, x_166, x_165, x_168);
x_171 = l_Lean_NameMap_contains___redArg(x_170, x_149);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
lean_free_object(x_161);
lean_free_object(x_154);
lean_inc(x_159);
x_172 = l_Lean_ErrorExplanation_processDoc(x_159);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_122);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_ctor_get(x_174, 1);
x_178 = l_Lean_Syntax_getArg(x_117, x_148);
lean_dec(x_117);
x_179 = l_Lean_Syntax_getRange_x3f(x_178, x_171);
lean_dec(x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_free_object(x_174);
lean_dec(x_176);
lean_ctor_set_tag(x_172, 3);
lean_ctor_set(x_172, 0, x_177);
x_180 = l_Lean_MessageData_ofFormat(x_172);
x_181 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_180, x_151, x_152, x_164);
return x_181;
}
else
{
uint8_t x_182; 
lean_free_object(x_172);
x_182 = !lean_is_exclusive(x_179);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_179, 0);
x_184 = lean_ctor_get(x_151, 1);
lean_inc(x_184);
x_185 = !lean_is_exclusive(x_183);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_186 = lean_ctor_get(x_183, 0);
x_187 = lean_ctor_get(x_183, 1);
lean_dec(x_187);
lean_inc(x_184);
x_188 = l_Lean_FileMap_toPosition(x_184, x_186);
lean_dec(x_186);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = lean_ctor_get(x_188, 1);
lean_dec(x_191);
x_192 = lean_nat_add(x_190, x_176);
lean_dec(x_176);
lean_dec(x_190);
lean_inc(x_192);
lean_ctor_set(x_188, 1, x_116);
lean_ctor_set(x_188, 0, x_192);
lean_inc(x_184);
x_193 = l_Lean_FileMap_ofPosition(x_184, x_188);
x_194 = lean_nat_add(x_192, x_148);
lean_dec(x_192);
lean_ctor_set(x_174, 1, x_116);
lean_ctor_set(x_174, 0, x_194);
x_195 = l_Lean_FileMap_ofPosition(x_184, x_174);
lean_ctor_set(x_183, 1, x_195);
lean_ctor_set(x_183, 0, x_193);
x_196 = l_Lean_Syntax_ofRange(x_183, x_135);
lean_ctor_set_tag(x_179, 3);
lean_ctor_set(x_179, 0, x_177);
x_197 = l_Lean_MessageData_ofFormat(x_179);
x_198 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_196, x_197, x_151, x_152, x_164);
lean_dec(x_196);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_199 = lean_ctor_get(x_188, 0);
lean_inc(x_199);
lean_dec(x_188);
x_200 = lean_nat_add(x_199, x_176);
lean_dec(x_176);
lean_dec(x_199);
lean_inc(x_200);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_116);
lean_inc(x_184);
x_202 = l_Lean_FileMap_ofPosition(x_184, x_201);
x_203 = lean_nat_add(x_200, x_148);
lean_dec(x_200);
lean_ctor_set(x_174, 1, x_116);
lean_ctor_set(x_174, 0, x_203);
x_204 = l_Lean_FileMap_ofPosition(x_184, x_174);
lean_ctor_set(x_183, 1, x_204);
lean_ctor_set(x_183, 0, x_202);
x_205 = l_Lean_Syntax_ofRange(x_183, x_135);
lean_ctor_set_tag(x_179, 3);
lean_ctor_set(x_179, 0, x_177);
x_206 = l_Lean_MessageData_ofFormat(x_179);
x_207 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_205, x_206, x_151, x_152, x_164);
lean_dec(x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_208 = lean_ctor_get(x_183, 0);
lean_inc(x_208);
lean_dec(x_183);
lean_inc(x_184);
x_209 = l_Lean_FileMap_toPosition(x_184, x_208);
lean_dec(x_208);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
x_212 = lean_nat_add(x_210, x_176);
lean_dec(x_176);
lean_dec(x_210);
lean_inc(x_212);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_116);
lean_inc(x_184);
x_214 = l_Lean_FileMap_ofPosition(x_184, x_213);
x_215 = lean_nat_add(x_212, x_148);
lean_dec(x_212);
lean_ctor_set(x_174, 1, x_116);
lean_ctor_set(x_174, 0, x_215);
x_216 = l_Lean_FileMap_ofPosition(x_184, x_174);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Lean_Syntax_ofRange(x_217, x_135);
lean_ctor_set_tag(x_179, 3);
lean_ctor_set(x_179, 0, x_177);
x_219 = l_Lean_MessageData_ofFormat(x_179);
x_220 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_218, x_219, x_151, x_152, x_164);
lean_dec(x_218);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_221 = lean_ctor_get(x_179, 0);
lean_inc(x_221);
lean_dec(x_179);
x_222 = lean_ctor_get(x_151, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_224 = x_221;
} else {
 lean_dec_ref(x_221);
 x_224 = lean_box(0);
}
lean_inc(x_222);
x_225 = l_Lean_FileMap_toPosition(x_222, x_223);
lean_dec(x_223);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
x_228 = lean_nat_add(x_226, x_176);
lean_dec(x_176);
lean_dec(x_226);
lean_inc(x_228);
if (lean_is_scalar(x_227)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_227;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_116);
lean_inc(x_222);
x_230 = l_Lean_FileMap_ofPosition(x_222, x_229);
x_231 = lean_nat_add(x_228, x_148);
lean_dec(x_228);
lean_ctor_set(x_174, 1, x_116);
lean_ctor_set(x_174, 0, x_231);
x_232 = l_Lean_FileMap_ofPosition(x_222, x_174);
if (lean_is_scalar(x_224)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_224;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Lean_Syntax_ofRange(x_233, x_135);
x_235 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_235, 0, x_177);
x_236 = l_Lean_MessageData_ofFormat(x_235);
x_237 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_234, x_236, x_151, x_152, x_164);
lean_dec(x_234);
return x_237;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_174, 0);
x_239 = lean_ctor_get(x_174, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_174);
x_240 = l_Lean_Syntax_getArg(x_117, x_148);
lean_dec(x_117);
x_241 = l_Lean_Syntax_getRange_x3f(x_240, x_171);
lean_dec(x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_238);
lean_ctor_set_tag(x_172, 3);
lean_ctor_set(x_172, 0, x_239);
x_242 = l_Lean_MessageData_ofFormat(x_172);
x_243 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_242, x_151, x_152, x_164);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_free_object(x_172);
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 x_245 = x_241;
} else {
 lean_dec_ref(x_241);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_151, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_248 = x_244;
} else {
 lean_dec_ref(x_244);
 x_248 = lean_box(0);
}
lean_inc(x_246);
x_249 = l_Lean_FileMap_toPosition(x_246, x_247);
lean_dec(x_247);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_251 = x_249;
} else {
 lean_dec_ref(x_249);
 x_251 = lean_box(0);
}
x_252 = lean_nat_add(x_250, x_238);
lean_dec(x_238);
lean_dec(x_250);
lean_inc(x_252);
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_116);
lean_inc(x_246);
x_254 = l_Lean_FileMap_ofPosition(x_246, x_253);
x_255 = lean_nat_add(x_252, x_148);
lean_dec(x_252);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_116);
x_257 = l_Lean_FileMap_ofPosition(x_246, x_256);
if (lean_is_scalar(x_248)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_248;
}
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_Syntax_ofRange(x_258, x_135);
if (lean_is_scalar(x_245)) {
 x_260 = lean_alloc_ctor(3, 1, 0);
} else {
 x_260 = x_245;
 lean_ctor_set_tag(x_260, 3);
}
lean_ctor_set(x_260, 0, x_239);
x_261 = l_Lean_MessageData_ofFormat(x_260);
x_262 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_259, x_261, x_151, x_152, x_164);
lean_dec(x_259);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_ctor_get(x_172, 0);
lean_inc(x_263);
lean_dec(x_172);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
x_267 = l_Lean_Syntax_getArg(x_117, x_148);
lean_dec(x_117);
x_268 = l_Lean_Syntax_getRange_x3f(x_267, x_171);
lean_dec(x_267);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_266);
lean_dec(x_264);
x_269 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_269, 0, x_265);
x_270 = l_Lean_MessageData_ofFormat(x_269);
x_271 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_270, x_151, x_152, x_164);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_272 = lean_ctor_get(x_268, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_273 = x_268;
} else {
 lean_dec_ref(x_268);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_151, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 0);
lean_inc(x_275);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_276 = x_272;
} else {
 lean_dec_ref(x_272);
 x_276 = lean_box(0);
}
lean_inc(x_274);
x_277 = l_Lean_FileMap_toPosition(x_274, x_275);
lean_dec(x_275);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_279 = x_277;
} else {
 lean_dec_ref(x_277);
 x_279 = lean_box(0);
}
x_280 = lean_nat_add(x_278, x_264);
lean_dec(x_264);
lean_dec(x_278);
lean_inc(x_280);
if (lean_is_scalar(x_279)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_279;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_116);
lean_inc(x_274);
x_282 = l_Lean_FileMap_ofPosition(x_274, x_281);
x_283 = lean_nat_add(x_280, x_148);
lean_dec(x_280);
if (lean_is_scalar(x_266)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_266;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_116);
x_285 = l_Lean_FileMap_ofPosition(x_274, x_284);
if (lean_is_scalar(x_276)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_276;
}
lean_ctor_set(x_286, 0, x_282);
lean_ctor_set(x_286, 1, x_285);
x_287 = l_Lean_Syntax_ofRange(x_286, x_135);
if (lean_is_scalar(x_273)) {
 x_288 = lean_alloc_ctor(3, 1, 0);
} else {
 x_288 = x_273;
 lean_ctor_set_tag(x_288, 3);
}
lean_ctor_set(x_288, 0, x_265);
x_289 = l_Lean_MessageData_ofFormat(x_288);
x_290 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_287, x_289, x_151, x_152, x_164);
lean_dec(x_287);
return x_290;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_172);
lean_dec(x_117);
x_291 = lean_ctor_get(x_151, 1);
lean_inc(x_291);
lean_dec(x_151);
x_292 = l_Lean_Syntax_getPos_x3f(x_122, x_171);
if (lean_obj_tag(x_292) == 0)
{
x_123 = x_159;
x_124 = x_152;
x_125 = x_291;
x_126 = x_149;
x_127 = x_150;
x_128 = x_164;
x_129 = x_171;
x_130 = x_116;
goto block_133;
}
else
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec(x_292);
x_123 = x_159;
x_124 = x_152;
x_125 = x_291;
x_126 = x_149;
x_127 = x_150;
x_128 = x_164;
x_129 = x_171;
x_130 = x_293;
goto block_133;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_117);
x_294 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
x_295 = l_Lean_MessageData_ofName(x_149);
lean_ctor_set_tag(x_161, 7);
lean_ctor_set(x_161, 1, x_295);
lean_ctor_set(x_161, 0, x_294);
x_296 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
lean_ctor_set_tag(x_154, 7);
lean_ctor_set(x_154, 1, x_296);
lean_ctor_set(x_154, 0, x_161);
x_297 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_154, x_151, x_152, x_164);
lean_dec(x_122);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_161, 0);
x_299 = lean_ctor_get(x_161, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_161);
x_300 = lean_ctor_get(x_298, 0);
lean_inc(x_300);
lean_dec(x_298);
x_301 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get_uint8(x_302, sizeof(void*)*3);
lean_dec(x_302);
x_304 = lean_box(0);
x_305 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_304, x_301, x_300, x_303);
x_306 = l_Lean_NameMap_contains___redArg(x_305, x_149);
lean_dec(x_305);
if (x_306 == 0)
{
lean_object* x_307; 
lean_free_object(x_154);
lean_inc(x_159);
x_307 = l_Lean_ErrorExplanation_processDoc(x_159);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_122);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_309 = x_307;
} else {
 lean_dec_ref(x_307);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 x_312 = x_308;
} else {
 lean_dec_ref(x_308);
 x_312 = lean_box(0);
}
x_313 = l_Lean_Syntax_getArg(x_117, x_148);
lean_dec(x_117);
x_314 = l_Lean_Syntax_getRange_x3f(x_313, x_306);
lean_dec(x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_312);
lean_dec(x_310);
if (lean_is_scalar(x_309)) {
 x_315 = lean_alloc_ctor(3, 1, 0);
} else {
 x_315 = x_309;
 lean_ctor_set_tag(x_315, 3);
}
lean_ctor_set(x_315, 0, x_311);
x_316 = l_Lean_MessageData_ofFormat(x_315);
x_317 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_316, x_151, x_152, x_299);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_309);
x_318 = lean_ctor_get(x_314, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 x_319 = x_314;
} else {
 lean_dec_ref(x_314);
 x_319 = lean_box(0);
}
x_320 = lean_ctor_get(x_151, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_318, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_322 = x_318;
} else {
 lean_dec_ref(x_318);
 x_322 = lean_box(0);
}
lean_inc(x_320);
x_323 = l_Lean_FileMap_toPosition(x_320, x_321);
lean_dec(x_321);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
x_326 = lean_nat_add(x_324, x_310);
lean_dec(x_310);
lean_dec(x_324);
lean_inc(x_326);
if (lean_is_scalar(x_325)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_325;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_116);
lean_inc(x_320);
x_328 = l_Lean_FileMap_ofPosition(x_320, x_327);
x_329 = lean_nat_add(x_326, x_148);
lean_dec(x_326);
if (lean_is_scalar(x_312)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_312;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_116);
x_331 = l_Lean_FileMap_ofPosition(x_320, x_330);
if (lean_is_scalar(x_322)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_322;
}
lean_ctor_set(x_332, 0, x_328);
lean_ctor_set(x_332, 1, x_331);
x_333 = l_Lean_Syntax_ofRange(x_332, x_135);
if (lean_is_scalar(x_319)) {
 x_334 = lean_alloc_ctor(3, 1, 0);
} else {
 x_334 = x_319;
 lean_ctor_set_tag(x_334, 3);
}
lean_ctor_set(x_334, 0, x_311);
x_335 = l_Lean_MessageData_ofFormat(x_334);
x_336 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_333, x_335, x_151, x_152, x_299);
lean_dec(x_333);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_307);
lean_dec(x_117);
x_337 = lean_ctor_get(x_151, 1);
lean_inc(x_337);
lean_dec(x_151);
x_338 = l_Lean_Syntax_getPos_x3f(x_122, x_306);
if (lean_obj_tag(x_338) == 0)
{
x_123 = x_159;
x_124 = x_152;
x_125 = x_337;
x_126 = x_149;
x_127 = x_150;
x_128 = x_299;
x_129 = x_306;
x_130 = x_116;
goto block_133;
}
else
{
lean_object* x_339; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec(x_338);
x_123 = x_159;
x_124 = x_152;
x_125 = x_337;
x_126 = x_149;
x_127 = x_150;
x_128 = x_299;
x_129 = x_306;
x_130 = x_339;
goto block_133;
}
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_117);
x_340 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
x_341 = l_Lean_MessageData_ofName(x_149);
x_342 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
x_343 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
lean_ctor_set_tag(x_154, 7);
lean_ctor_set(x_154, 1, x_343);
lean_ctor_set(x_154, 0, x_342);
x_344 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_154, x_151, x_152, x_299);
lean_dec(x_122);
return x_344;
}
}
}
else
{
uint8_t x_345; 
lean_free_object(x_154);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_122);
lean_dec(x_117);
x_345 = !lean_is_exclusive(x_158);
if (x_345 == 0)
{
return x_158;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_158, 0);
x_347 = lean_ctor_get(x_158, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_158);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_154, 1);
lean_inc(x_349);
lean_dec(x_154);
lean_inc(x_151);
x_350 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(x_117, x_151, x_152, x_349);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_st_ref_get(x_152, x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_356 = x_353;
} else {
 lean_dec_ref(x_353);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_354, 0);
lean_inc(x_357);
lean_dec(x_354);
x_358 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get_uint8(x_359, sizeof(void*)*3);
lean_dec(x_359);
x_361 = lean_box(0);
x_362 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_361, x_358, x_357, x_360);
x_363 = l_Lean_NameMap_contains___redArg(x_362, x_149);
lean_dec(x_362);
if (x_363 == 0)
{
lean_object* x_364; 
lean_dec(x_356);
lean_inc(x_351);
x_364 = l_Lean_ErrorExplanation_processDoc(x_351);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_351);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_122);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 x_366 = x_364;
} else {
 lean_dec_ref(x_364);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_365, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_369 = x_365;
} else {
 lean_dec_ref(x_365);
 x_369 = lean_box(0);
}
x_370 = l_Lean_Syntax_getArg(x_117, x_148);
lean_dec(x_117);
x_371 = l_Lean_Syntax_getRange_x3f(x_370, x_363);
lean_dec(x_370);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_369);
lean_dec(x_367);
if (lean_is_scalar(x_366)) {
 x_372 = lean_alloc_ctor(3, 1, 0);
} else {
 x_372 = x_366;
 lean_ctor_set_tag(x_372, 3);
}
lean_ctor_set(x_372, 0, x_368);
x_373 = l_Lean_MessageData_ofFormat(x_372);
x_374 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_373, x_151, x_152, x_355);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_366);
x_375 = lean_ctor_get(x_371, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_151, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_375, 0);
lean_inc(x_378);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_379 = x_375;
} else {
 lean_dec_ref(x_375);
 x_379 = lean_box(0);
}
lean_inc(x_377);
x_380 = l_Lean_FileMap_toPosition(x_377, x_378);
lean_dec(x_378);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
x_383 = lean_nat_add(x_381, x_367);
lean_dec(x_367);
lean_dec(x_381);
lean_inc(x_383);
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_116);
lean_inc(x_377);
x_385 = l_Lean_FileMap_ofPosition(x_377, x_384);
x_386 = lean_nat_add(x_383, x_148);
lean_dec(x_383);
if (lean_is_scalar(x_369)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_369;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_116);
x_388 = l_Lean_FileMap_ofPosition(x_377, x_387);
if (lean_is_scalar(x_379)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_379;
}
lean_ctor_set(x_389, 0, x_385);
lean_ctor_set(x_389, 1, x_388);
x_390 = l_Lean_Syntax_ofRange(x_389, x_135);
if (lean_is_scalar(x_376)) {
 x_391 = lean_alloc_ctor(3, 1, 0);
} else {
 x_391 = x_376;
 lean_ctor_set_tag(x_391, 3);
}
lean_ctor_set(x_391, 0, x_368);
x_392 = l_Lean_MessageData_ofFormat(x_391);
x_393 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_390, x_392, x_151, x_152, x_355);
lean_dec(x_390);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; 
lean_dec(x_364);
lean_dec(x_117);
x_394 = lean_ctor_get(x_151, 1);
lean_inc(x_394);
lean_dec(x_151);
x_395 = l_Lean_Syntax_getPos_x3f(x_122, x_363);
if (lean_obj_tag(x_395) == 0)
{
x_123 = x_351;
x_124 = x_152;
x_125 = x_394;
x_126 = x_149;
x_127 = x_150;
x_128 = x_355;
x_129 = x_363;
x_130 = x_116;
goto block_133;
}
else
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec(x_395);
x_123 = x_351;
x_124 = x_152;
x_125 = x_394;
x_126 = x_149;
x_127 = x_150;
x_128 = x_355;
x_129 = x_363;
x_130 = x_396;
goto block_133;
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_351);
lean_dec(x_150);
lean_dec(x_117);
x_397 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
x_398 = l_Lean_MessageData_ofName(x_149);
if (lean_is_scalar(x_356)) {
 x_399 = lean_alloc_ctor(7, 2, 0);
} else {
 x_399 = x_356;
 lean_ctor_set_tag(x_399, 7);
}
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
x_400 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
x_401 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
x_402 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_401, x_151, x_152, x_355);
lean_dec(x_122);
return x_402;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_122);
lean_dec(x_117);
x_403 = lean_ctor_get(x_350, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_350, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_405 = x_350;
} else {
 lean_dec_ref(x_350);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; 
x_444 = lean_ctor_get(x_141, 0);
x_445 = lean_ctor_get(x_141, 1);
x_446 = lean_ctor_get(x_2, 0);
x_447 = lean_ctor_get(x_2, 1);
x_448 = lean_ctor_get(x_2, 2);
x_449 = lean_ctor_get(x_2, 3);
x_450 = lean_ctor_get(x_2, 4);
x_451 = lean_ctor_get(x_2, 5);
x_452 = lean_ctor_get(x_2, 7);
x_453 = lean_ctor_get(x_2, 8);
x_454 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_inc(x_448);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_2);
x_455 = lean_ctor_get(x_444, 0);
lean_inc(x_455);
lean_dec(x_444);
x_456 = lean_unsigned_to_nat(1u);
x_523 = l_Lean_Syntax_getArg(x_1, x_456);
x_524 = lean_unsigned_to_nat(3u);
x_525 = l_Lean_Syntax_getArg(x_1, x_524);
lean_dec(x_1);
x_526 = l_Lean_replaceRef(x_523, x_139);
lean_dec(x_139);
lean_dec(x_523);
x_527 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_527, 0, x_446);
lean_ctor_set(x_527, 1, x_447);
lean_ctor_set(x_527, 2, x_448);
lean_ctor_set(x_527, 3, x_449);
lean_ctor_set(x_527, 4, x_450);
lean_ctor_set(x_527, 5, x_451);
lean_ctor_set(x_527, 6, x_526);
lean_ctor_set(x_527, 7, x_452);
lean_ctor_set(x_527, 8, x_453);
lean_ctor_set_uint8(x_527, sizeof(void*)*9, x_454);
x_528 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10;
x_529 = l_Lean_Environment_contains(x_455, x_528, x_135);
if (x_529 == 0)
{
lean_object* x_530; lean_object* x_531; 
lean_dec(x_525);
lean_free_object(x_141);
lean_free_object(x_137);
lean_dec(x_122);
lean_dec(x_117);
x_530 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12;
x_531 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_530, x_527, x_3, x_445);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15;
x_533 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed), 10, 2);
lean_closure_set(x_533, 0, x_525);
lean_closure_set(x_533, 1, x_532);
x_534 = l_Lean_Elab_Command_runTermElabM___redArg(x_533, x_527, x_3, x_445);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = l_Lean_Syntax_getId(x_122);
x_538 = l_Lean_Name_isAnonymous(x_537);
if (x_538 == 0)
{
uint8_t x_539; 
x_539 = l_Lean_Name_hasMacroScopes(x_537);
if (x_539 == 0)
{
lean_object* x_540; uint8_t x_541; 
x_540 = l_Lean_Name_getNumParts(x_537);
x_541 = lean_nat_dec_eq(x_540, x_121);
lean_dec(x_540);
if (x_541 == 0)
{
if (x_135 == 0)
{
lean_free_object(x_141);
lean_free_object(x_137);
x_457 = x_537;
x_458 = x_535;
x_459 = x_527;
x_460 = x_3;
x_461 = x_536;
goto block_522;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_535);
lean_dec(x_117);
x_542 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
x_543 = l_Lean_MessageData_ofName(x_537);
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_543);
lean_ctor_set(x_141, 0, x_542);
x_544 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19;
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_544);
lean_ctor_set(x_137, 0, x_141);
x_545 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22;
x_546 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_546, 0, x_137);
lean_ctor_set(x_546, 1, x_545);
x_547 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_546, x_527, x_3, x_536);
lean_dec(x_122);
return x_547;
}
}
else
{
lean_free_object(x_141);
lean_free_object(x_137);
x_457 = x_537;
x_458 = x_535;
x_459 = x_527;
x_460 = x_3;
x_461 = x_536;
goto block_522;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_537);
lean_dec(x_535);
lean_dec(x_117);
x_548 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
lean_inc(x_122);
x_549 = l_Lean_MessageData_ofSyntax(x_122);
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_549);
lean_ctor_set(x_141, 0, x_548);
x_550 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__24;
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_550);
lean_ctor_set(x_137, 0, x_141);
x_551 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_137, x_527, x_3, x_536);
lean_dec(x_122);
return x_551;
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_537);
lean_dec(x_535);
lean_dec(x_117);
x_552 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__26;
lean_inc(x_122);
x_553 = l_Lean_MessageData_ofSyntax(x_122);
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_553);
lean_ctor_set(x_141, 0, x_552);
x_554 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_554);
lean_ctor_set(x_137, 0, x_141);
x_555 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_137, x_527, x_3, x_536);
lean_dec(x_122);
return x_555;
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_527);
lean_free_object(x_141);
lean_free_object(x_137);
lean_dec(x_122);
lean_dec(x_117);
x_556 = lean_ctor_get(x_534, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_534, 1);
lean_inc(x_557);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_558 = x_534;
} else {
 lean_dec_ref(x_534);
 x_558 = lean_box(0);
}
if (lean_is_scalar(x_558)) {
 x_559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_559 = x_558;
}
lean_ctor_set(x_559, 0, x_556);
lean_ctor_set(x_559, 1, x_557);
return x_559;
}
}
block_522:
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_inc(x_459);
x_462 = l_Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(x_117, x_459, x_460, x_461);
x_463 = lean_ctor_get(x_462, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_464 = x_462;
} else {
 lean_dec_ref(x_462);
 x_464 = lean_box(0);
}
lean_inc(x_459);
x_465 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(x_117, x_459, x_460, x_463);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_468 = lean_st_ref_get(x_460, x_467);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_471 = x_468;
} else {
 lean_dec_ref(x_468);
 x_471 = lean_box(0);
}
x_472 = lean_ctor_get(x_469, 0);
lean_inc(x_472);
lean_dec(x_469);
x_473 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get_uint8(x_474, sizeof(void*)*3);
lean_dec(x_474);
x_476 = lean_box(0);
x_477 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_476, x_473, x_472, x_475);
x_478 = l_Lean_NameMap_contains___redArg(x_477, x_457);
lean_dec(x_477);
if (x_478 == 0)
{
lean_object* x_479; 
lean_dec(x_471);
lean_dec(x_464);
lean_inc(x_466);
x_479 = l_Lean_ErrorExplanation_processDoc(x_466);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_466);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_122);
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 x_481 = x_479;
} else {
 lean_dec_ref(x_479);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_480, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_484 = x_480;
} else {
 lean_dec_ref(x_480);
 x_484 = lean_box(0);
}
x_485 = l_Lean_Syntax_getArg(x_117, x_456);
lean_dec(x_117);
x_486 = l_Lean_Syntax_getRange_x3f(x_485, x_478);
lean_dec(x_485);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_484);
lean_dec(x_482);
if (lean_is_scalar(x_481)) {
 x_487 = lean_alloc_ctor(3, 1, 0);
} else {
 x_487 = x_481;
 lean_ctor_set_tag(x_487, 3);
}
lean_ctor_set(x_487, 0, x_483);
x_488 = l_Lean_MessageData_ofFormat(x_487);
x_489 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_488, x_459, x_460, x_470);
return x_489;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_481);
x_490 = lean_ctor_get(x_486, 0);
lean_inc(x_490);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_491 = x_486;
} else {
 lean_dec_ref(x_486);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_459, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_490, 0);
lean_inc(x_493);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_494 = x_490;
} else {
 lean_dec_ref(x_490);
 x_494 = lean_box(0);
}
lean_inc(x_492);
x_495 = l_Lean_FileMap_toPosition(x_492, x_493);
lean_dec(x_493);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_497 = x_495;
} else {
 lean_dec_ref(x_495);
 x_497 = lean_box(0);
}
x_498 = lean_nat_add(x_496, x_482);
lean_dec(x_482);
lean_dec(x_496);
lean_inc(x_498);
if (lean_is_scalar(x_497)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_497;
}
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_116);
lean_inc(x_492);
x_500 = l_Lean_FileMap_ofPosition(x_492, x_499);
x_501 = lean_nat_add(x_498, x_456);
lean_dec(x_498);
if (lean_is_scalar(x_484)) {
 x_502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_502 = x_484;
}
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_116);
x_503 = l_Lean_FileMap_ofPosition(x_492, x_502);
if (lean_is_scalar(x_494)) {
 x_504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_504 = x_494;
}
lean_ctor_set(x_504, 0, x_500);
lean_ctor_set(x_504, 1, x_503);
x_505 = l_Lean_Syntax_ofRange(x_504, x_135);
if (lean_is_scalar(x_491)) {
 x_506 = lean_alloc_ctor(3, 1, 0);
} else {
 x_506 = x_491;
 lean_ctor_set_tag(x_506, 3);
}
lean_ctor_set(x_506, 0, x_483);
x_507 = l_Lean_MessageData_ofFormat(x_506);
x_508 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_505, x_507, x_459, x_460, x_470);
lean_dec(x_505);
return x_508;
}
}
else
{
lean_object* x_509; lean_object* x_510; 
lean_dec(x_479);
lean_dec(x_117);
x_509 = lean_ctor_get(x_459, 1);
lean_inc(x_509);
lean_dec(x_459);
x_510 = l_Lean_Syntax_getPos_x3f(x_122, x_478);
if (lean_obj_tag(x_510) == 0)
{
x_123 = x_466;
x_124 = x_460;
x_125 = x_509;
x_126 = x_457;
x_127 = x_458;
x_128 = x_470;
x_129 = x_478;
x_130 = x_116;
goto block_133;
}
else
{
lean_object* x_511; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
lean_dec(x_510);
x_123 = x_466;
x_124 = x_460;
x_125 = x_509;
x_126 = x_457;
x_127 = x_458;
x_128 = x_470;
x_129 = x_478;
x_130 = x_511;
goto block_133;
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec(x_466);
lean_dec(x_458);
lean_dec(x_117);
x_512 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
x_513 = l_Lean_MessageData_ofName(x_457);
if (lean_is_scalar(x_471)) {
 x_514 = lean_alloc_ctor(7, 2, 0);
} else {
 x_514 = x_471;
 lean_ctor_set_tag(x_514, 7);
}
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
x_515 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
if (lean_is_scalar(x_464)) {
 x_516 = lean_alloc_ctor(7, 2, 0);
} else {
 x_516 = x_464;
 lean_ctor_set_tag(x_516, 7);
}
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
x_517 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_516, x_459, x_460, x_470);
lean_dec(x_122);
return x_517;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_464);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_122);
lean_dec(x_117);
x_518 = lean_ctor_get(x_465, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_465, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_520 = x_465;
} else {
 lean_dec_ref(x_465);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_519);
return x_521;
}
}
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; 
x_560 = lean_ctor_get(x_141, 0);
x_561 = lean_ctor_get(x_141, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_141);
x_562 = lean_ctor_get(x_2, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_2, 1);
lean_inc(x_563);
x_564 = lean_ctor_get(x_2, 2);
lean_inc(x_564);
x_565 = lean_ctor_get(x_2, 3);
lean_inc(x_565);
x_566 = lean_ctor_get(x_2, 4);
lean_inc(x_566);
x_567 = lean_ctor_get(x_2, 5);
lean_inc(x_567);
x_568 = lean_ctor_get(x_2, 7);
lean_inc(x_568);
x_569 = lean_ctor_get(x_2, 8);
lean_inc(x_569);
x_570 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 x_571 = x_2;
} else {
 lean_dec_ref(x_2);
 x_571 = lean_box(0);
}
x_572 = lean_ctor_get(x_560, 0);
lean_inc(x_572);
lean_dec(x_560);
x_573 = lean_unsigned_to_nat(1u);
x_640 = l_Lean_Syntax_getArg(x_1, x_573);
x_641 = lean_unsigned_to_nat(3u);
x_642 = l_Lean_Syntax_getArg(x_1, x_641);
lean_dec(x_1);
x_643 = l_Lean_replaceRef(x_640, x_139);
lean_dec(x_139);
lean_dec(x_640);
if (lean_is_scalar(x_571)) {
 x_644 = lean_alloc_ctor(0, 9, 1);
} else {
 x_644 = x_571;
}
lean_ctor_set(x_644, 0, x_562);
lean_ctor_set(x_644, 1, x_563);
lean_ctor_set(x_644, 2, x_564);
lean_ctor_set(x_644, 3, x_565);
lean_ctor_set(x_644, 4, x_566);
lean_ctor_set(x_644, 5, x_567);
lean_ctor_set(x_644, 6, x_643);
lean_ctor_set(x_644, 7, x_568);
lean_ctor_set(x_644, 8, x_569);
lean_ctor_set_uint8(x_644, sizeof(void*)*9, x_570);
x_645 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10;
x_646 = l_Lean_Environment_contains(x_572, x_645, x_135);
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; 
lean_dec(x_642);
lean_free_object(x_137);
lean_dec(x_122);
lean_dec(x_117);
x_647 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12;
x_648 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_647, x_644, x_3, x_561);
return x_648;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15;
x_650 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed), 10, 2);
lean_closure_set(x_650, 0, x_642);
lean_closure_set(x_650, 1, x_649);
x_651 = l_Lean_Elab_Command_runTermElabM___redArg(x_650, x_644, x_3, x_561);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
x_654 = l_Lean_Syntax_getId(x_122);
x_655 = l_Lean_Name_isAnonymous(x_654);
if (x_655 == 0)
{
uint8_t x_656; 
x_656 = l_Lean_Name_hasMacroScopes(x_654);
if (x_656 == 0)
{
lean_object* x_657; uint8_t x_658; 
x_657 = l_Lean_Name_getNumParts(x_654);
x_658 = lean_nat_dec_eq(x_657, x_121);
lean_dec(x_657);
if (x_658 == 0)
{
if (x_135 == 0)
{
lean_free_object(x_137);
x_574 = x_654;
x_575 = x_652;
x_576 = x_644;
x_577 = x_3;
x_578 = x_653;
goto block_639;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
lean_dec(x_652);
lean_dec(x_117);
x_659 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
x_660 = l_Lean_MessageData_ofName(x_654);
x_661 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
x_662 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19;
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_662);
lean_ctor_set(x_137, 0, x_661);
x_663 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22;
x_664 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_664, 0, x_137);
lean_ctor_set(x_664, 1, x_663);
x_665 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_664, x_644, x_3, x_653);
lean_dec(x_122);
return x_665;
}
}
else
{
lean_free_object(x_137);
x_574 = x_654;
x_575 = x_652;
x_576 = x_644;
x_577 = x_3;
x_578 = x_653;
goto block_639;
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_117);
x_666 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
lean_inc(x_122);
x_667 = l_Lean_MessageData_ofSyntax(x_122);
x_668 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
x_669 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__24;
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_669);
lean_ctor_set(x_137, 0, x_668);
x_670 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_137, x_644, x_3, x_653);
lean_dec(x_122);
return x_670;
}
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_117);
x_671 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__26;
lean_inc(x_122);
x_672 = l_Lean_MessageData_ofSyntax(x_122);
x_673 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_673, 0, x_671);
lean_ctor_set(x_673, 1, x_672);
x_674 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_674);
lean_ctor_set(x_137, 0, x_673);
x_675 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_137, x_644, x_3, x_653);
lean_dec(x_122);
return x_675;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_dec(x_644);
lean_free_object(x_137);
lean_dec(x_122);
lean_dec(x_117);
x_676 = lean_ctor_get(x_651, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_651, 1);
lean_inc(x_677);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 lean_ctor_release(x_651, 1);
 x_678 = x_651;
} else {
 lean_dec_ref(x_651);
 x_678 = lean_box(0);
}
if (lean_is_scalar(x_678)) {
 x_679 = lean_alloc_ctor(1, 2, 0);
} else {
 x_679 = x_678;
}
lean_ctor_set(x_679, 0, x_676);
lean_ctor_set(x_679, 1, x_677);
return x_679;
}
}
block_639:
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_inc(x_576);
x_579 = l_Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(x_117, x_576, x_577, x_578);
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_581 = x_579;
} else {
 lean_dec_ref(x_579);
 x_581 = lean_box(0);
}
lean_inc(x_576);
x_582 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(x_117, x_576, x_577, x_580);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_585 = lean_st_ref_get(x_577, x_584);
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_588 = x_585;
} else {
 lean_dec_ref(x_585);
 x_588 = lean_box(0);
}
x_589 = lean_ctor_get(x_586, 0);
lean_inc(x_589);
lean_dec(x_586);
x_590 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get_uint8(x_591, sizeof(void*)*3);
lean_dec(x_591);
x_593 = lean_box(0);
x_594 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_593, x_590, x_589, x_592);
x_595 = l_Lean_NameMap_contains___redArg(x_594, x_574);
lean_dec(x_594);
if (x_595 == 0)
{
lean_object* x_596; 
lean_dec(x_588);
lean_dec(x_581);
lean_inc(x_583);
x_596 = l_Lean_ErrorExplanation_processDoc(x_583);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_583);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_122);
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 x_598 = x_596;
} else {
 lean_dec_ref(x_596);
 x_598 = lean_box(0);
}
x_599 = lean_ctor_get(x_597, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_597, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_601 = x_597;
} else {
 lean_dec_ref(x_597);
 x_601 = lean_box(0);
}
x_602 = l_Lean_Syntax_getArg(x_117, x_573);
lean_dec(x_117);
x_603 = l_Lean_Syntax_getRange_x3f(x_602, x_595);
lean_dec(x_602);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_601);
lean_dec(x_599);
if (lean_is_scalar(x_598)) {
 x_604 = lean_alloc_ctor(3, 1, 0);
} else {
 x_604 = x_598;
 lean_ctor_set_tag(x_604, 3);
}
lean_ctor_set(x_604, 0, x_600);
x_605 = l_Lean_MessageData_ofFormat(x_604);
x_606 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_605, x_576, x_577, x_587);
return x_606;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_598);
x_607 = lean_ctor_get(x_603, 0);
lean_inc(x_607);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 x_608 = x_603;
} else {
 lean_dec_ref(x_603);
 x_608 = lean_box(0);
}
x_609 = lean_ctor_get(x_576, 1);
lean_inc(x_609);
x_610 = lean_ctor_get(x_607, 0);
lean_inc(x_610);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_611 = x_607;
} else {
 lean_dec_ref(x_607);
 x_611 = lean_box(0);
}
lean_inc(x_609);
x_612 = l_Lean_FileMap_toPosition(x_609, x_610);
lean_dec(x_610);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_614 = x_612;
} else {
 lean_dec_ref(x_612);
 x_614 = lean_box(0);
}
x_615 = lean_nat_add(x_613, x_599);
lean_dec(x_599);
lean_dec(x_613);
lean_inc(x_615);
if (lean_is_scalar(x_614)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_614;
}
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_116);
lean_inc(x_609);
x_617 = l_Lean_FileMap_ofPosition(x_609, x_616);
x_618 = lean_nat_add(x_615, x_573);
lean_dec(x_615);
if (lean_is_scalar(x_601)) {
 x_619 = lean_alloc_ctor(0, 2, 0);
} else {
 x_619 = x_601;
}
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_116);
x_620 = l_Lean_FileMap_ofPosition(x_609, x_619);
if (lean_is_scalar(x_611)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_611;
}
lean_ctor_set(x_621, 0, x_617);
lean_ctor_set(x_621, 1, x_620);
x_622 = l_Lean_Syntax_ofRange(x_621, x_135);
if (lean_is_scalar(x_608)) {
 x_623 = lean_alloc_ctor(3, 1, 0);
} else {
 x_623 = x_608;
 lean_ctor_set_tag(x_623, 3);
}
lean_ctor_set(x_623, 0, x_600);
x_624 = l_Lean_MessageData_ofFormat(x_623);
x_625 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_622, x_624, x_576, x_577, x_587);
lean_dec(x_622);
return x_625;
}
}
else
{
lean_object* x_626; lean_object* x_627; 
lean_dec(x_596);
lean_dec(x_117);
x_626 = lean_ctor_get(x_576, 1);
lean_inc(x_626);
lean_dec(x_576);
x_627 = l_Lean_Syntax_getPos_x3f(x_122, x_595);
if (lean_obj_tag(x_627) == 0)
{
x_123 = x_583;
x_124 = x_577;
x_125 = x_626;
x_126 = x_574;
x_127 = x_575;
x_128 = x_587;
x_129 = x_595;
x_130 = x_116;
goto block_133;
}
else
{
lean_object* x_628; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
lean_dec(x_627);
x_123 = x_583;
x_124 = x_577;
x_125 = x_626;
x_126 = x_574;
x_127 = x_575;
x_128 = x_587;
x_129 = x_595;
x_130 = x_628;
goto block_133;
}
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_583);
lean_dec(x_575);
lean_dec(x_117);
x_629 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
x_630 = l_Lean_MessageData_ofName(x_574);
if (lean_is_scalar(x_588)) {
 x_631 = lean_alloc_ctor(7, 2, 0);
} else {
 x_631 = x_588;
 lean_ctor_set_tag(x_631, 7);
}
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
x_632 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
if (lean_is_scalar(x_581)) {
 x_633 = lean_alloc_ctor(7, 2, 0);
} else {
 x_633 = x_581;
 lean_ctor_set_tag(x_633, 7);
}
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
x_634 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_633, x_576, x_577, x_587);
lean_dec(x_122);
return x_634;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_581);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_122);
lean_dec(x_117);
x_635 = lean_ctor_get(x_582, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_582, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_637 = x_582;
} else {
 lean_dec_ref(x_582);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_635);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; uint8_t x_770; 
x_680 = lean_ctor_get(x_137, 0);
x_681 = lean_ctor_get(x_137, 1);
lean_inc(x_681);
lean_inc(x_680);
lean_dec(x_137);
x_682 = lean_st_ref_get(x_3, x_681);
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_685 = x_682;
} else {
 lean_dec_ref(x_682);
 x_685 = lean_box(0);
}
x_686 = lean_ctor_get(x_2, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_2, 1);
lean_inc(x_687);
x_688 = lean_ctor_get(x_2, 2);
lean_inc(x_688);
x_689 = lean_ctor_get(x_2, 3);
lean_inc(x_689);
x_690 = lean_ctor_get(x_2, 4);
lean_inc(x_690);
x_691 = lean_ctor_get(x_2, 5);
lean_inc(x_691);
x_692 = lean_ctor_get(x_2, 7);
lean_inc(x_692);
x_693 = lean_ctor_get(x_2, 8);
lean_inc(x_693);
x_694 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 x_695 = x_2;
} else {
 lean_dec_ref(x_2);
 x_695 = lean_box(0);
}
x_696 = lean_ctor_get(x_683, 0);
lean_inc(x_696);
lean_dec(x_683);
x_697 = lean_unsigned_to_nat(1u);
x_764 = l_Lean_Syntax_getArg(x_1, x_697);
x_765 = lean_unsigned_to_nat(3u);
x_766 = l_Lean_Syntax_getArg(x_1, x_765);
lean_dec(x_1);
x_767 = l_Lean_replaceRef(x_764, x_680);
lean_dec(x_680);
lean_dec(x_764);
if (lean_is_scalar(x_695)) {
 x_768 = lean_alloc_ctor(0, 9, 1);
} else {
 x_768 = x_695;
}
lean_ctor_set(x_768, 0, x_686);
lean_ctor_set(x_768, 1, x_687);
lean_ctor_set(x_768, 2, x_688);
lean_ctor_set(x_768, 3, x_689);
lean_ctor_set(x_768, 4, x_690);
lean_ctor_set(x_768, 5, x_691);
lean_ctor_set(x_768, 6, x_767);
lean_ctor_set(x_768, 7, x_692);
lean_ctor_set(x_768, 8, x_693);
lean_ctor_set_uint8(x_768, sizeof(void*)*9, x_694);
x_769 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10;
x_770 = l_Lean_Environment_contains(x_696, x_769, x_135);
if (x_770 == 0)
{
lean_object* x_771; lean_object* x_772; 
lean_dec(x_766);
lean_dec(x_685);
lean_dec(x_122);
lean_dec(x_117);
x_771 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12;
x_772 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_771, x_768, x_3, x_684);
return x_772;
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_773 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15;
x_774 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed), 10, 2);
lean_closure_set(x_774, 0, x_766);
lean_closure_set(x_774, 1, x_773);
x_775 = l_Lean_Elab_Command_runTermElabM___redArg(x_774, x_768, x_3, x_684);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; uint8_t x_779; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
x_778 = l_Lean_Syntax_getId(x_122);
x_779 = l_Lean_Name_isAnonymous(x_778);
if (x_779 == 0)
{
uint8_t x_780; 
x_780 = l_Lean_Name_hasMacroScopes(x_778);
if (x_780 == 0)
{
lean_object* x_781; uint8_t x_782; 
x_781 = l_Lean_Name_getNumParts(x_778);
x_782 = lean_nat_dec_eq(x_781, x_121);
lean_dec(x_781);
if (x_782 == 0)
{
if (x_135 == 0)
{
lean_dec(x_685);
x_698 = x_778;
x_699 = x_776;
x_700 = x_768;
x_701 = x_3;
x_702 = x_777;
goto block_763;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
lean_dec(x_776);
lean_dec(x_117);
x_783 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
x_784 = l_Lean_MessageData_ofName(x_778);
if (lean_is_scalar(x_685)) {
 x_785 = lean_alloc_ctor(7, 2, 0);
} else {
 x_785 = x_685;
 lean_ctor_set_tag(x_785, 7);
}
lean_ctor_set(x_785, 0, x_783);
lean_ctor_set(x_785, 1, x_784);
x_786 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19;
x_787 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_787, 0, x_785);
lean_ctor_set(x_787, 1, x_786);
x_788 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22;
x_789 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_789, 0, x_787);
lean_ctor_set(x_789, 1, x_788);
x_790 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_789, x_768, x_3, x_777);
lean_dec(x_122);
return x_790;
}
}
else
{
lean_dec(x_685);
x_698 = x_778;
x_699 = x_776;
x_700 = x_768;
x_701 = x_3;
x_702 = x_777;
goto block_763;
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_778);
lean_dec(x_776);
lean_dec(x_117);
x_791 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17;
lean_inc(x_122);
x_792 = l_Lean_MessageData_ofSyntax(x_122);
if (lean_is_scalar(x_685)) {
 x_793 = lean_alloc_ctor(7, 2, 0);
} else {
 x_793 = x_685;
 lean_ctor_set_tag(x_793, 7);
}
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
x_794 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__24;
x_795 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_795, 0, x_793);
lean_ctor_set(x_795, 1, x_794);
x_796 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_795, x_768, x_3, x_777);
lean_dec(x_122);
return x_796;
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_778);
lean_dec(x_776);
lean_dec(x_117);
x_797 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__26;
lean_inc(x_122);
x_798 = l_Lean_MessageData_ofSyntax(x_122);
if (lean_is_scalar(x_685)) {
 x_799 = lean_alloc_ctor(7, 2, 0);
} else {
 x_799 = x_685;
 lean_ctor_set_tag(x_799, 7);
}
lean_ctor_set(x_799, 0, x_797);
lean_ctor_set(x_799, 1, x_798);
x_800 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
x_801 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
x_802 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_801, x_768, x_3, x_777);
lean_dec(x_122);
return x_802;
}
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
lean_dec(x_768);
lean_dec(x_685);
lean_dec(x_122);
lean_dec(x_117);
x_803 = lean_ctor_get(x_775, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_775, 1);
lean_inc(x_804);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_805 = x_775;
} else {
 lean_dec_ref(x_775);
 x_805 = lean_box(0);
}
if (lean_is_scalar(x_805)) {
 x_806 = lean_alloc_ctor(1, 2, 0);
} else {
 x_806 = x_805;
}
lean_ctor_set(x_806, 0, x_803);
lean_ctor_set(x_806, 1, x_804);
return x_806;
}
}
block_763:
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_inc(x_700);
x_703 = l_Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(x_117, x_700, x_701, x_702);
x_704 = lean_ctor_get(x_703, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 x_705 = x_703;
} else {
 lean_dec_ref(x_703);
 x_705 = lean_box(0);
}
lean_inc(x_700);
x_706 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(x_117, x_700, x_701, x_704);
if (lean_obj_tag(x_706) == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_717; lean_object* x_718; uint8_t x_719; 
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_706, 1);
lean_inc(x_708);
lean_dec(x_706);
x_709 = lean_st_ref_get(x_701, x_708);
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_712 = x_709;
} else {
 lean_dec_ref(x_709);
 x_712 = lean_box(0);
}
x_713 = lean_ctor_get(x_710, 0);
lean_inc(x_713);
lean_dec(x_710);
x_714 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get_uint8(x_715, sizeof(void*)*3);
lean_dec(x_715);
x_717 = lean_box(0);
x_718 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_717, x_714, x_713, x_716);
x_719 = l_Lean_NameMap_contains___redArg(x_718, x_698);
lean_dec(x_718);
if (x_719 == 0)
{
lean_object* x_720; 
lean_dec(x_712);
lean_dec(x_705);
lean_inc(x_707);
x_720 = l_Lean_ErrorExplanation_processDoc(x_707);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
lean_dec(x_707);
lean_dec(x_699);
lean_dec(x_698);
lean_dec(x_122);
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 x_722 = x_720;
} else {
 lean_dec_ref(x_720);
 x_722 = lean_box(0);
}
x_723 = lean_ctor_get(x_721, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_721, 1);
lean_inc(x_724);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_725 = x_721;
} else {
 lean_dec_ref(x_721);
 x_725 = lean_box(0);
}
x_726 = l_Lean_Syntax_getArg(x_117, x_697);
lean_dec(x_117);
x_727 = l_Lean_Syntax_getRange_x3f(x_726, x_719);
lean_dec(x_726);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_725);
lean_dec(x_723);
if (lean_is_scalar(x_722)) {
 x_728 = lean_alloc_ctor(3, 1, 0);
} else {
 x_728 = x_722;
 lean_ctor_set_tag(x_728, 3);
}
lean_ctor_set(x_728, 0, x_724);
x_729 = l_Lean_MessageData_ofFormat(x_728);
x_730 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_729, x_700, x_701, x_711);
return x_730;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_722);
x_731 = lean_ctor_get(x_727, 0);
lean_inc(x_731);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 x_732 = x_727;
} else {
 lean_dec_ref(x_727);
 x_732 = lean_box(0);
}
x_733 = lean_ctor_get(x_700, 1);
lean_inc(x_733);
x_734 = lean_ctor_get(x_731, 0);
lean_inc(x_734);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_735 = x_731;
} else {
 lean_dec_ref(x_731);
 x_735 = lean_box(0);
}
lean_inc(x_733);
x_736 = l_Lean_FileMap_toPosition(x_733, x_734);
lean_dec(x_734);
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_738 = x_736;
} else {
 lean_dec_ref(x_736);
 x_738 = lean_box(0);
}
x_739 = lean_nat_add(x_737, x_723);
lean_dec(x_723);
lean_dec(x_737);
lean_inc(x_739);
if (lean_is_scalar(x_738)) {
 x_740 = lean_alloc_ctor(0, 2, 0);
} else {
 x_740 = x_738;
}
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set(x_740, 1, x_116);
lean_inc(x_733);
x_741 = l_Lean_FileMap_ofPosition(x_733, x_740);
x_742 = lean_nat_add(x_739, x_697);
lean_dec(x_739);
if (lean_is_scalar(x_725)) {
 x_743 = lean_alloc_ctor(0, 2, 0);
} else {
 x_743 = x_725;
}
lean_ctor_set(x_743, 0, x_742);
lean_ctor_set(x_743, 1, x_116);
x_744 = l_Lean_FileMap_ofPosition(x_733, x_743);
if (lean_is_scalar(x_735)) {
 x_745 = lean_alloc_ctor(0, 2, 0);
} else {
 x_745 = x_735;
}
lean_ctor_set(x_745, 0, x_741);
lean_ctor_set(x_745, 1, x_744);
x_746 = l_Lean_Syntax_ofRange(x_745, x_135);
if (lean_is_scalar(x_732)) {
 x_747 = lean_alloc_ctor(3, 1, 0);
} else {
 x_747 = x_732;
 lean_ctor_set_tag(x_747, 3);
}
lean_ctor_set(x_747, 0, x_724);
x_748 = l_Lean_MessageData_ofFormat(x_747);
x_749 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_746, x_748, x_700, x_701, x_711);
lean_dec(x_746);
return x_749;
}
}
else
{
lean_object* x_750; lean_object* x_751; 
lean_dec(x_720);
lean_dec(x_117);
x_750 = lean_ctor_get(x_700, 1);
lean_inc(x_750);
lean_dec(x_700);
x_751 = l_Lean_Syntax_getPos_x3f(x_122, x_719);
if (lean_obj_tag(x_751) == 0)
{
x_123 = x_707;
x_124 = x_701;
x_125 = x_750;
x_126 = x_698;
x_127 = x_699;
x_128 = x_711;
x_129 = x_719;
x_130 = x_116;
goto block_133;
}
else
{
lean_object* x_752; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
lean_dec(x_751);
x_123 = x_707;
x_124 = x_701;
x_125 = x_750;
x_126 = x_698;
x_127 = x_699;
x_128 = x_711;
x_129 = x_719;
x_130 = x_752;
goto block_133;
}
}
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_707);
lean_dec(x_699);
lean_dec(x_117);
x_753 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7;
x_754 = l_Lean_MessageData_ofName(x_698);
if (lean_is_scalar(x_712)) {
 x_755 = lean_alloc_ctor(7, 2, 0);
} else {
 x_755 = x_712;
 lean_ctor_set_tag(x_755, 7);
}
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
x_756 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9;
if (lean_is_scalar(x_705)) {
 x_757 = lean_alloc_ctor(7, 2, 0);
} else {
 x_757 = x_705;
 lean_ctor_set_tag(x_757, 7);
}
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_756);
x_758 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at___Lean_Elab_Command_elabCommand_go_spec__1_spec__3___redArg(x_122, x_757, x_700, x_701, x_711);
lean_dec(x_122);
return x_758;
}
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec(x_705);
lean_dec(x_700);
lean_dec(x_699);
lean_dec(x_698);
lean_dec(x_122);
lean_dec(x_117);
x_759 = lean_ctor_get(x_706, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_706, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_706)) {
 lean_ctor_release(x_706, 0);
 lean_ctor_release(x_706, 1);
 x_761 = x_706;
} else {
 lean_dec_ref(x_706);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_759);
lean_ctor_set(x_762, 1, x_760);
return x_762;
}
}
}
}
block_133:
{
lean_object* x_131; 
x_131 = l_Lean_Syntax_getTailPos_x3f(x_122, x_129);
lean_dec(x_122);
if (lean_obj_tag(x_131) == 0)
{
lean_inc(x_130);
x_5 = x_123;
x_6 = x_124;
x_7 = x_125;
x_8 = x_126;
x_9 = x_130;
x_10 = x_127;
x_11 = x_128;
x_12 = x_130;
goto block_112;
}
else
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec(x_131);
x_5 = x_123;
x_6 = x_124;
x_7 = x_125;
x_8 = x_126;
x_9 = x_130;
x_10 = x_127;
x_11 = x_128;
x_12 = x_132;
goto block_112;
}
}
}
}
block_112:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Command_getMainModule___redArg(x_6, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_st_ref_take(x_6, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_19, 0);
x_23 = l_Lean_DeclarationRange_ofStringPositions(x_7, x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_ctor_set(x_17, 1, x_23);
lean_ctor_set(x_17, 0, x_15);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_10);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_8);
x_27 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_25, x_22, x_13);
lean_ctor_set(x_19, 0, x_27);
x_28 = lean_st_ref_set(x_6, x_19, x_21);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_35 = lean_ctor_get(x_17, 1);
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
x_38 = lean_ctor_get(x_19, 2);
x_39 = lean_ctor_get(x_19, 3);
x_40 = lean_ctor_get(x_19, 4);
x_41 = lean_ctor_get(x_19, 5);
x_42 = lean_ctor_get(x_19, 6);
x_43 = lean_ctor_get(x_19, 7);
x_44 = lean_ctor_get(x_19, 8);
x_45 = lean_ctor_get(x_19, 9);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_46 = l_Lean_DeclarationRange_ofStringPositions(x_7, x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_ctor_set(x_17, 1, x_46);
lean_ctor_set(x_17, 0, x_15);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_17);
x_48 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_10);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_13, 1, x_49);
lean_ctor_set(x_13, 0, x_8);
x_50 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_48, x_36, x_13);
x_51 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_37);
lean_ctor_set(x_51, 2, x_38);
lean_ctor_set(x_51, 3, x_39);
lean_ctor_set(x_51, 4, x_40);
lean_ctor_set(x_51, 5, x_41);
lean_ctor_set(x_51, 6, x_42);
lean_ctor_set(x_51, 7, x_43);
lean_ctor_set(x_51, 8, x_44);
lean_ctor_set(x_51, 9, x_45);
x_52 = lean_st_ref_set(x_6, x_51, x_35);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_57 = lean_ctor_get(x_17, 0);
x_58 = lean_ctor_get(x_17, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_17);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 6);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 7);
lean_inc(x_66);
x_67 = lean_ctor_get(x_57, 8);
lean_inc(x_67);
x_68 = lean_ctor_get(x_57, 9);
lean_inc(x_68);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 lean_ctor_release(x_57, 7);
 lean_ctor_release(x_57, 8);
 lean_ctor_release(x_57, 9);
 x_69 = x_57;
} else {
 lean_dec_ref(x_57);
 x_69 = lean_box(0);
}
x_70 = l_Lean_DeclarationRange_ofStringPositions(x_7, x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_15);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_5);
lean_ctor_set(x_74, 1, x_10);
lean_ctor_set(x_74, 2, x_72);
lean_ctor_set(x_13, 1, x_74);
lean_ctor_set(x_13, 0, x_8);
x_75 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_73, x_59, x_13);
if (lean_is_scalar(x_69)) {
 x_76 = lean_alloc_ctor(0, 10, 0);
} else {
 x_76 = x_69;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_60);
lean_ctor_set(x_76, 2, x_61);
lean_ctor_set(x_76, 3, x_62);
lean_ctor_set(x_76, 4, x_63);
lean_ctor_set(x_76, 5, x_64);
lean_ctor_set(x_76, 6, x_65);
lean_ctor_set(x_76, 7, x_66);
lean_ctor_set(x_76, 8, x_67);
lean_ctor_set(x_76, 9, x_68);
x_77 = lean_st_ref_set(x_6, x_76, x_58);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_82 = lean_ctor_get(x_13, 0);
x_83 = lean_ctor_get(x_13, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_13);
x_84 = lean_st_ref_take(x_6, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 4);
lean_inc(x_92);
x_93 = lean_ctor_get(x_85, 5);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 6);
lean_inc(x_94);
x_95 = lean_ctor_get(x_85, 7);
lean_inc(x_95);
x_96 = lean_ctor_get(x_85, 8);
lean_inc(x_96);
x_97 = lean_ctor_get(x_85, 9);
lean_inc(x_97);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 lean_ctor_release(x_85, 4);
 lean_ctor_release(x_85, 5);
 lean_ctor_release(x_85, 6);
 lean_ctor_release(x_85, 7);
 lean_ctor_release(x_85, 8);
 lean_ctor_release(x_85, 9);
 x_98 = x_85;
} else {
 lean_dec_ref(x_85);
 x_98 = lean_box(0);
}
x_99 = l_Lean_DeclarationRange_ofStringPositions(x_7, x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
if (lean_is_scalar(x_87)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_87;
}
lean_ctor_set(x_100, 0, x_82);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0;
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_5);
lean_ctor_set(x_103, 1, x_10);
lean_ctor_set(x_103, 2, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_8);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_102, x_88, x_104);
if (lean_is_scalar(x_98)) {
 x_106 = lean_alloc_ctor(0, 10, 0);
} else {
 x_106 = x_98;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_89);
lean_ctor_set(x_106, 2, x_90);
lean_ctor_set(x_106, 3, x_91);
lean_ctor_set(x_106, 4, x_92);
lean_ctor_set(x_106, 5, x_93);
lean_ctor_set(x_106, 6, x_94);
lean_ctor_set(x_106, 7, x_95);
lean_ctor_set(x_106, 8, x_96);
lean_ctor_set(x_106, 9, x_97);
x_107 = lean_st_ref_set(x_6, x_106, x_86);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0_spec__0(x_1, x_2, x_3, x_4, x_11, x_12, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_validateDocComment___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
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
static lean_object* _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
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
x_1 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1;
x_2 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
x_3 = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1;
x_4 = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0;
x_3 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3;
x_4 = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
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
l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0 = _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0();
lean_mark_persistent(l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0);
l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1 = _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1();
lean_mark_persistent(l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1);
l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2 = _init_l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2();
lean_mark_persistent(l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2);
if (builtin) {res = l_Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0);
l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1 = _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1();
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
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0);
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
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__26 = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__26();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__26);
l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap = _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap();
lean_mark_persistent(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0);
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
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__3);
l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4 = _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__4);
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
}l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__0 = _init_l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__0();
lean_mark_persistent(l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__0);
l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__1 = _init_l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__1();
lean_mark_persistent(l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__1);
l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__2 = _init_l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__2();
lean_mark_persistent(l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__2);
l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__3 = _init_l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__3();
lean_mark_persistent(l_Lean_getDocStringText___at___Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___closed__3);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0);
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
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__22);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__23 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__23();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__23);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__24 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__24();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__24);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__25 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__25();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__25);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__26 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__26();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__26);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1);
l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2 = _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2();
lean_mark_persistent(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__2);
if (builtin) {res = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
