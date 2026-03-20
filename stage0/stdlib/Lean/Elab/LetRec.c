// Lean compiler output
// Module: Lean.Elab.LetRec
// Imports: public import Lean.Elab.MutualDef
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_doc_verso;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_Elab_TerminationHints_none;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBindersEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___redArg(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_toAttributeKind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
extern lean_object* l_Lean_regularInitAttr;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkBodyInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withInfoContext_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withAuxDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1;
static lean_once_cell_t l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2;
static lean_once_cell_t l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__3 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Unexpected Termination.suffix syntax: "};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " of kind "};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "decreasingBy"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__7 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__7_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 199, 246, 58, 76, 113, 58, 46)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unexpected `decreasing_by` syntax"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__9 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__9_value;
static lean_once_cell_t l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__11 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__11_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__11_value),LEAN_SCALAR_PTR_LITERAL(86, 48, 154, 136, 39, 235, 76, 224)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "coinductiveFixpoint"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__13 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__13_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__13_value),LEAN_SCALAR_PTR_LITERAL(129, 219, 184, 173, 172, 251, 220, 64)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "inductiveFixpoint"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__15 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__15_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__15_value),LEAN_SCALAR_PTR_LITERAL(12, 66, 190, 73, 6, 174, 236, 45)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16_value;
static const lean_array_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__17 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__17_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `termination_by` syntax"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__18 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__18_value;
static lean_once_cell_t l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "no extra parameters bounds, please omit the `=>`"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__20 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__20_value;
static lean_once_cell_t l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "terminationBy"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__22 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__22_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__22_value),LEAN_SCALAR_PTR_LITERAL(20, 221, 175, 114, 26, 111, 13, 165)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23_value;
static const lean_string_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "terminationBy\?"};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__24 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__24_value;
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__24_value),LEAN_SCALAR_PTR_LITERAL(224, 143, 0, 201, 195, 223, 93, 180)}};
static const lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25 = (const lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Unknown attribute `["};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]`"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unknown attribute"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40_spec__45(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40_spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__0 = (const lean_object*)&l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__34(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1;
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__2 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__2_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3;
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "private declaration `"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__4 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__4_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "` is a reserved name"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__4(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "a private declaration `"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "a non-private declaration `"};
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___boxed, .m_arity = 9, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___closed__0 = (const lean_object*)&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "failed to infer 'let rec' declaration type"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "'let rec' expressions must be named"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__4_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letEqnsDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__6_value),LEAN_SCALAR_PTR_LITERAL(82, 210, 72, 51, 179, 245, 26, 94)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "patterns are not allowed in 'let rec' expressions"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___closed__0 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "letrec"};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 19, 234, 96, 193, 73, 5, 238)}};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabLetRec"};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__2 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(101, 182, 190, 124, 44, 87, 65, 222)}};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(132) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__0_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__1_value),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__3_value),((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__4_value),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_box(0);
v___x_16_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v___x_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg(){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg___closed__0);
v___x_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg___boxed(lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8(lean_object* v_00_u03b1_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___boxed(lean_object* v_00_u03b1_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8(v_00_u03b1_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
return v_res_40_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__0(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(1);
v___x_42_ = l_Lean_MessageData_ofFormat(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__3(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__2));
v___x_47_ = l_Lean_MessageData_ofFormat(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27(lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
return v_x_48_;
}
else
{
lean_object* v_head_50_; lean_object* v_tail_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_73_; 
v_head_50_ = lean_ctor_get(v_x_49_, 0);
v_tail_51_ = lean_ctor_get(v_x_49_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_x_49_);
if (v_isSharedCheck_73_ == 0)
{
v___x_53_ = v_x_49_;
v_isShared_54_ = v_isSharedCheck_73_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_tail_51_);
lean_inc(v_head_50_);
lean_dec(v_x_49_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_73_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_before_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_71_; 
v_before_55_ = lean_ctor_get(v_head_50_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v_head_50_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v_head_50_, 1);
lean_dec(v_unused_72_);
v___x_57_ = v_head_50_;
v_isShared_58_ = v_isSharedCheck_71_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_before_55_);
lean_dec(v_head_50_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_71_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_61_; 
v___x_59_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__0);
if (v_isShared_58_ == 0)
{
lean_ctor_set_tag(v___x_57_, 7);
lean_ctor_set(v___x_57_, 1, v___x_59_);
lean_ctor_set(v___x_57_, 0, v_x_48_);
v___x_61_ = v___x_57_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_x_48_);
lean_ctor_set(v_reuseFailAlloc_70_, 1, v___x_59_);
v___x_61_ = v_reuseFailAlloc_70_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__3);
if (v_isShared_54_ == 0)
{
lean_ctor_set_tag(v___x_53_, 7);
lean_ctor_set(v___x_53_, 1, v___x_62_);
lean_ctor_set(v___x_53_, 0, v___x_61_);
v___x_64_ = v___x_53_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_69_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = l_Lean_MessageData_ofSyntax(v_before_55_);
v___x_66_ = l_Lean_indentD(v___x_65_);
v___x_67_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v_x_48_ = v___x_67_;
v_x_49_ = v_tail_51_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__2(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__1));
v___x_78_ = l_Lean_MessageData_ofFormat(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg(lean_object* v_msgData_79_, lean_object* v_macroStack_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_options_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_options_83_ = lean_ctor_get(v___y_81_, 2);
v___x_84_ = l_Lean_Elab_pp_macroStack;
v___x_85_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_options_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; 
lean_dec(v_macroStack_80_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v_msgData_79_);
return v___x_86_;
}
else
{
if (lean_obj_tag(v_macroStack_80_) == 0)
{
lean_object* v___x_87_; 
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v_msgData_79_);
return v___x_87_;
}
else
{
lean_object* v_head_88_; lean_object* v_after_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_104_; 
v_head_88_ = lean_ctor_get(v_macroStack_80_, 0);
lean_inc(v_head_88_);
v_after_89_ = lean_ctor_get(v_head_88_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v_head_88_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_head_88_, 0);
lean_dec(v_unused_105_);
v___x_91_ = v_head_88_;
v_isShared_92_ = v_isSharedCheck_104_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_after_89_);
lean_dec(v_head_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_104_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27___closed__0);
if (v_isShared_92_ == 0)
{
lean_ctor_set_tag(v___x_91_, 7);
lean_ctor_set(v___x_91_, 1, v___x_93_);
lean_ctor_set(v___x_91_, 0, v_msgData_79_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_msgData_79_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_103_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_msgData_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_96_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___closed__2);
v___x_97_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = l_Lean_MessageData_ofSyntax(v_after_89_);
v___x_99_ = l_Lean_indentD(v___x_98_);
v_msgData_100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_100_, 0, v___x_97_);
lean_ctor_set(v_msgData_100_, 1, v___x_99_);
v___x_101_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18_spec__27(v_msgData_100_, v_macroStack_80_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg___boxed(lean_object* v_msgData_106_, lean_object* v_macroStack_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg(v_msgData_106_, v_macroStack_107_, v___y_108_);
lean_dec_ref(v___y_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(lean_object* v_msgData_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; lean_object* v_env_118_; lean_object* v___x_119_; lean_object* v_mctx_120_; lean_object* v_lctx_121_; lean_object* v_options_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_117_ = lean_st_ref_get(v___y_115_);
v_env_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc_ref(v_env_118_);
lean_dec(v___x_117_);
v___x_119_ = lean_st_ref_get(v___y_113_);
v_mctx_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc_ref(v_mctx_120_);
lean_dec(v___x_119_);
v_lctx_121_ = lean_ctor_get(v___y_112_, 2);
v_options_122_ = lean_ctor_get(v___y_114_, 2);
lean_inc_ref(v_options_122_);
lean_inc_ref(v_lctx_121_);
v___x_123_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_123_, 0, v_env_118_);
lean_ctor_set(v___x_123_, 1, v_mctx_120_);
lean_ctor_set(v___x_123_, 2, v_lctx_121_);
lean_ctor_set(v___x_123_, 3, v_options_122_);
v___x_124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v_msgData_111_);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___boxed(lean_object* v_msgData_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(v_msgData_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_ref_141_; lean_object* v___x_142_; lean_object* v_a_143_; lean_object* v_macroStack_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_ref_141_ = lean_ctor_get(v___y_138_, 5);
v___x_142_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(v_msg_133_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref(v___x_142_);
v_macroStack_144_ = lean_ctor_get(v___y_134_, 1);
lean_inc(v_macroStack_144_);
lean_dec_ref(v___y_134_);
lean_inc(v_macroStack_144_);
v___x_145_ = l_Lean_Elab_getBetterRef(v_ref_141_, v_macroStack_144_);
v___x_146_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg(v_a_143_, v_macroStack_144_, v___y_138_);
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_155_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_145_);
lean_ctor_set(v___x_151_, 1, v_a_147_);
if (v_isShared_150_ == 0)
{
lean_ctor_set_tag(v___x_149_, 1);
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg___boxed(lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v_msg_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(lean_object* v_ref_165_, lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_fileName_174_; lean_object* v_fileMap_175_; lean_object* v_options_176_; lean_object* v_currRecDepth_177_; lean_object* v_maxRecDepth_178_; lean_object* v_ref_179_; lean_object* v_currNamespace_180_; lean_object* v_openDecls_181_; lean_object* v_initHeartbeats_182_; lean_object* v_maxHeartbeats_183_; lean_object* v_quotContext_184_; lean_object* v_currMacroScope_185_; uint8_t v_diag_186_; lean_object* v_cancelTk_x3f_187_; uint8_t v_suppressElabErrors_188_; lean_object* v_inheritedTraceOptions_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_198_; 
v_fileName_174_ = lean_ctor_get(v___y_171_, 0);
v_fileMap_175_ = lean_ctor_get(v___y_171_, 1);
v_options_176_ = lean_ctor_get(v___y_171_, 2);
v_currRecDepth_177_ = lean_ctor_get(v___y_171_, 3);
v_maxRecDepth_178_ = lean_ctor_get(v___y_171_, 4);
v_ref_179_ = lean_ctor_get(v___y_171_, 5);
v_currNamespace_180_ = lean_ctor_get(v___y_171_, 6);
v_openDecls_181_ = lean_ctor_get(v___y_171_, 7);
v_initHeartbeats_182_ = lean_ctor_get(v___y_171_, 8);
v_maxHeartbeats_183_ = lean_ctor_get(v___y_171_, 9);
v_quotContext_184_ = lean_ctor_get(v___y_171_, 10);
v_currMacroScope_185_ = lean_ctor_get(v___y_171_, 11);
v_diag_186_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*14);
v_cancelTk_x3f_187_ = lean_ctor_get(v___y_171_, 12);
v_suppressElabErrors_188_ = lean_ctor_get_uint8(v___y_171_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_189_ = lean_ctor_get(v___y_171_, 13);
v_isSharedCheck_198_ = !lean_is_exclusive(v___y_171_);
if (v_isSharedCheck_198_ == 0)
{
v___x_191_ = v___y_171_;
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_inheritedTraceOptions_189_);
lean_inc(v_cancelTk_x3f_187_);
lean_inc(v_currMacroScope_185_);
lean_inc(v_quotContext_184_);
lean_inc(v_maxHeartbeats_183_);
lean_inc(v_initHeartbeats_182_);
lean_inc(v_openDecls_181_);
lean_inc(v_currNamespace_180_);
lean_inc(v_ref_179_);
lean_inc(v_maxRecDepth_178_);
lean_inc(v_currRecDepth_177_);
lean_inc(v_options_176_);
lean_inc(v_fileMap_175_);
lean_inc(v_fileName_174_);
lean_dec(v___y_171_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_ref_193_; lean_object* v___x_195_; 
v_ref_193_ = l_Lean_replaceRef(v_ref_165_, v_ref_179_);
lean_dec(v_ref_179_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 5, v_ref_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_fileName_174_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_fileMap_175_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_options_176_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_currRecDepth_177_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v_maxRecDepth_178_);
lean_ctor_set(v_reuseFailAlloc_197_, 5, v_ref_193_);
lean_ctor_set(v_reuseFailAlloc_197_, 6, v_currNamespace_180_);
lean_ctor_set(v_reuseFailAlloc_197_, 7, v_openDecls_181_);
lean_ctor_set(v_reuseFailAlloc_197_, 8, v_initHeartbeats_182_);
lean_ctor_set(v_reuseFailAlloc_197_, 9, v_maxHeartbeats_183_);
lean_ctor_set(v_reuseFailAlloc_197_, 10, v_quotContext_184_);
lean_ctor_set(v_reuseFailAlloc_197_, 11, v_currMacroScope_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 12, v_cancelTk_x3f_187_);
lean_ctor_set(v_reuseFailAlloc_197_, 13, v_inheritedTraceOptions_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_197_, sizeof(void*)*14, v_diag_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_197_, sizeof(void*)*14 + 1, v_suppressElabErrors_188_);
v___x_195_ = v_reuseFailAlloc_197_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v_msg_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___x_195_, v___y_172_);
lean_dec_ref(v___x_195_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg___boxed(lean_object* v_ref_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_ref_199_, v_msg_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec(v_ref_199_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(lean_object* v_stx_209_, lean_object* v___y_210_){
_start:
{
uint8_t v___x_212_; lean_object* v___x_213_; 
v___x_212_ = 0;
v___x_213_ = l_Lean_Syntax_getRange_x3f(v_stx_209_, v___x_212_);
if (lean_obj_tag(v___x_213_) == 1)
{
lean_object* v_val_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_226_; 
v_val_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_226_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_226_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_val_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_226_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_fileMap_218_; lean_object* v_start_219_; lean_object* v_stop_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v_fileMap_218_ = lean_ctor_get(v___y_210_, 1);
lean_inc_ref(v_fileMap_218_);
lean_dec_ref(v___y_210_);
v_start_219_ = lean_ctor_get(v_val_214_, 0);
lean_inc(v_start_219_);
v_stop_220_ = lean_ctor_get(v_val_214_, 1);
lean_inc(v_stop_220_);
lean_dec(v_val_214_);
v___x_221_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_218_, v_start_219_, v_stop_220_);
lean_dec(v_stop_220_);
lean_dec(v_start_219_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_221_);
v___x_223_ = v___x_216_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v___x_213_);
lean_dec_ref(v___y_210_);
v___x_227_ = lean_box(0);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg___boxed(lean_object* v_stx_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_stx_229_, v___y_230_);
lean_dec(v_stx_229_);
return v_res_232_;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_233_;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1);
v___x_237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1);
v___x_239_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_ctor_set(v___x_239_, 2, v___x_238_);
lean_ctor_set(v___x_239_, 3, v___x_238_);
lean_ctor_set(v___x_239_, 4, v___x_238_);
lean_ctor_set(v___x_239_, 5, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(lean_object* v_declName_240_, lean_object* v_declRanges_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
uint8_t v___x_245_; 
v___x_245_ = l_Lean_Name_isAnonymous(v_declName_240_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v_env_247_; lean_object* v_nextMacroScope_248_; lean_object* v_ngen_249_; lean_object* v_auxDeclNGen_250_; lean_object* v_traceState_251_; lean_object* v_messages_252_; lean_object* v_infoState_253_; lean_object* v_snapshotTasks_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_282_; 
v___x_246_ = lean_st_ref_take(v___y_243_);
v_env_247_ = lean_ctor_get(v___x_246_, 0);
v_nextMacroScope_248_ = lean_ctor_get(v___x_246_, 1);
v_ngen_249_ = lean_ctor_get(v___x_246_, 2);
v_auxDeclNGen_250_ = lean_ctor_get(v___x_246_, 3);
v_traceState_251_ = lean_ctor_get(v___x_246_, 4);
v_messages_252_ = lean_ctor_get(v___x_246_, 6);
v_infoState_253_ = lean_ctor_get(v___x_246_, 7);
v_snapshotTasks_254_ = lean_ctor_get(v___x_246_, 8);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___x_246_, 5);
lean_dec(v_unused_283_);
v___x_256_ = v___x_246_;
v_isShared_257_ = v_isSharedCheck_282_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_snapshotTasks_254_);
lean_inc(v_infoState_253_);
lean_inc(v_messages_252_);
lean_inc(v_traceState_251_);
lean_inc(v_auxDeclNGen_250_);
lean_inc(v_ngen_249_);
lean_inc(v_nextMacroScope_248_);
lean_inc(v_env_247_);
lean_dec(v___x_246_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_282_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_258_ = l_Lean_declRangeExt;
v___x_259_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_258_, v_env_247_, v_declName_240_, v_declRanges_241_);
v___x_260_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 5, v___x_260_);
lean_ctor_set(v___x_256_, 0, v___x_259_);
v___x_262_ = v___x_256_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_nextMacroScope_248_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_ngen_249_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_auxDeclNGen_250_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_traceState_251_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_messages_252_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_infoState_253_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_snapshotTasks_254_);
v___x_262_ = v_reuseFailAlloc_281_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_mctx_265_; lean_object* v_zetaDeltaFVarIds_266_; lean_object* v_postponed_267_; lean_object* v_diag_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_279_; 
v___x_263_ = lean_st_ref_set(v___y_243_, v___x_262_);
v___x_264_ = lean_st_ref_take(v___y_242_);
v_mctx_265_ = lean_ctor_get(v___x_264_, 0);
v_zetaDeltaFVarIds_266_ = lean_ctor_get(v___x_264_, 2);
v_postponed_267_ = lean_ctor_get(v___x_264_, 3);
v_diag_268_ = lean_ctor_get(v___x_264_, 4);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v___x_264_, 1);
lean_dec(v_unused_280_);
v___x_270_ = v___x_264_;
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_diag_268_);
lean_inc(v_postponed_267_);
lean_inc(v_zetaDeltaFVarIds_266_);
lean_inc(v_mctx_265_);
lean_dec(v___x_264_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_279_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 1, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_mctx_265_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_zetaDeltaFVarIds_266_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_postponed_267_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_diag_268_);
v___x_274_ = v_reuseFailAlloc_278_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_st_ref_set(v___y_242_, v___x_274_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
}
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec_ref(v_declRanges_241_);
lean_dec(v_declName_240_);
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___boxed(lean_object* v_declName_286_, lean_object* v_declRanges_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_286_, v_declRanges_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec(v___y_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(lean_object* v_declName_292_, lean_object* v_rangeStx_293_, lean_object* v_selectionRangeStx_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_319_; 
lean_inc_ref(v___y_299_);
v___x_302_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_rangeStx_293_, v___y_299_);
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_319_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_319_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_319_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
if (lean_obj_tag(v_a_303_) == 1)
{
lean_object* v_val_307_; lean_object* v___x_308_; lean_object* v_a_309_; lean_object* v_a_311_; 
lean_del_object(v___x_305_);
v_val_307_ = lean_ctor_get(v_a_303_, 0);
lean_inc(v_val_307_);
lean_dec_ref(v_a_303_);
v___x_308_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_selectionRangeStx_294_, v___y_299_);
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_308_);
if (lean_obj_tag(v_a_309_) == 0)
{
lean_inc(v_val_307_);
v_a_311_ = v_val_307_;
goto v___jp_310_;
}
else
{
lean_object* v_val_314_; 
v_val_314_ = lean_ctor_get(v_a_309_, 0);
lean_inc(v_val_314_);
lean_dec_ref(v_a_309_);
v_a_311_ = v_val_314_;
goto v___jp_310_;
}
v___jp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_val_307_);
lean_ctor_set(v___x_312_, 1, v_a_311_);
v___x_313_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_292_, v___x_312_, v___y_298_, v___y_300_);
return v___x_313_;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_dec(v_a_303_);
lean_dec_ref(v___y_299_);
lean_dec(v_declName_292_);
v___x_315_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_315_);
v___x_317_ = v___x_305_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2___boxed(lean_object* v_declName_320_, lean_object* v_rangeStx_321_, lean_object* v_selectionRangeStx_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(v_declName_320_, v_rangeStx_321_, v_selectionRangeStx_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v_selectionRangeStx_322_);
lean_dec(v_rangeStx_321_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0(lean_object* v___x_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_331_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0___boxed(lean_object* v___x_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0(v___x_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7(lean_object* v_00_u03b1_349_, lean_object* v_ref_350_, lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_ref_350_, v_msg_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___boxed(lean_object* v_00_u03b1_360_, lean_object* v_ref_361_, lean_object* v_msg_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7(v_00_u03b1_360_, v_ref_361_, v_msg_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec(v_ref_361_);
return v_res_370_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__9));
v___x_390_ = l_Lean_stringToMessageData(v___x_389_);
return v___x_390_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__18));
v___x_413_ = l_Lean_stringToMessageData(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__20));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(lean_object* v_stx_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
if (lean_obj_tag(v_stx_429_) == 0)
{
lean_object* v___x_437_; lean_object* v_terminationBy_x3f_x3f_438_; lean_object* v_terminationBy_x3f_439_; lean_object* v_partialFixpoint_x3f_440_; lean_object* v_decreasingBy_x3f_441_; lean_object* v_extraParams_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
v___x_437_ = l_Lean_Elab_TerminationHints_none;
v_terminationBy_x3f_x3f_438_ = lean_ctor_get(v___x_437_, 1);
v_terminationBy_x3f_439_ = lean_ctor_get(v___x_437_, 2);
v_partialFixpoint_x3f_440_ = lean_ctor_get(v___x_437_, 3);
v_decreasingBy_x3f_441_ = lean_ctor_get(v___x_437_, 4);
v_extraParams_442_ = lean_ctor_get(v___x_437_, 5);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v___x_437_, 0);
lean_dec(v_unused_451_);
v___x_444_ = v___x_437_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_extraParams_442_);
lean_inc(v_decreasingBy_x3f_441_);
lean_inc(v_partialFixpoint_x3f_440_);
lean_inc(v_terminationBy_x3f_439_);
lean_inc(v_terminationBy_x3f_x3f_438_);
lean_dec(v___x_437_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_stx_429_);
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_stx_429_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_terminationBy_x3f_x3f_438_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_terminationBy_x3f_439_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_partialFixpoint_x3f_440_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_decreasingBy_x3f_441_);
lean_ctor_set(v_reuseFailAlloc_449_, 5, v_extraParams_442_);
v___x_447_ = v_reuseFailAlloc_449_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; 
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4));
lean_inc(v_stx_429_);
v___x_453_ = l_Lean_Syntax_isOfKind(v_stx_429_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_454_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_455_ = lean_box(0);
lean_inc(v_stx_429_);
v___x_456_ = l_Lean_Syntax_formatStx(v_stx_429_, v___x_455_, v___x_453_);
v___x_457_ = l_Std_Format_defWidth;
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_459_ = l_Std_Format_pretty(v___x_456_, v___x_457_, v___x_458_, v___x_458_);
v___x_460_ = lean_string_append(v___x_454_, v___x_459_);
lean_dec_ref(v___x_459_);
v___x_461_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_462_ = lean_string_append(v___x_460_, v___x_461_);
lean_inc(v_stx_429_);
v___x_463_ = l_Lean_Syntax_getKind(v_stx_429_);
v___x_464_ = 1;
v___x_465_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_463_, v___x_464_);
v___x_466_ = lean_string_append(v___x_462_, v___x_465_);
lean_dec_ref(v___x_465_);
v___x_467_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
v___x_468_ = l_Lean_MessageData_ofFormat(v___x_467_);
v___x_469_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_429_, v___x_468_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec(v_stx_429_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v_partialFixpoint_x3f_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v_term_x3f_536_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v_term_x3f_552_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v_term_x3f_568_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v_val_575_; lean_object* v___y_576_; lean_object* v_terminationBy_x3f_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v_terminationBy_x3f_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; uint8_t v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; uint8_t v___y_643_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; uint8_t v___y_698_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v_s_713_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v_val_748_; lean_object* v___y_749_; lean_object* v_terminationBy_x3f_x3f_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v_d_x3f_839_; lean_object* v_t_x3f_848_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_886_ = l_Lean_Syntax_getArg(v_stx_429_, v___x_470_);
v___x_887_ = l_Lean_Syntax_isNone(v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_886_);
v___x_889_ = l_Lean_Syntax_matchesNull(v___x_886_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec(v___x_886_);
v___x_890_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_891_ = lean_box(0);
lean_inc(v_stx_429_);
v___x_892_ = l_Lean_Syntax_formatStx(v_stx_429_, v___x_891_, v___x_889_);
v___x_893_ = l_Std_Format_defWidth;
v___x_894_ = l_Std_Format_pretty(v___x_892_, v___x_893_, v___x_470_, v___x_470_);
v___x_895_ = lean_string_append(v___x_890_, v___x_894_);
lean_dec_ref(v___x_894_);
v___x_896_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_897_ = lean_string_append(v___x_895_, v___x_896_);
lean_inc(v_stx_429_);
v___x_898_ = l_Lean_Syntax_getKind(v_stx_429_);
v___x_899_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_898_, v___x_453_);
v___x_900_ = lean_string_append(v___x_897_, v___x_899_);
lean_dec_ref(v___x_899_);
v___x_901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
v___x_902_ = l_Lean_MessageData_ofFormat(v___x_901_);
v___x_903_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_429_, v___x_902_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec(v_stx_429_);
return v___x_903_;
}
else
{
lean_object* v_t_x3f_904_; lean_object* v___x_905_; 
v_t_x3f_904_ = l_Lean_Syntax_getArg(v___x_886_, v___x_470_);
lean_dec(v___x_886_);
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v_t_x3f_904_);
v_t_x3f_848_ = v___x_905_;
goto v___jp_847_;
}
}
else
{
lean_object* v___x_906_; 
lean_dec(v___x_886_);
v___x_906_ = lean_box(0);
v_t_x3f_848_ = v___x_906_;
goto v___jp_847_;
}
v___jp_471_:
{
lean_object* v___x_482_; 
v___x_482_ = lean_apply_7(v___y_481_, v___y_479_, v___y_473_, v___y_477_, v___y_476_, v___y_475_, v___y_478_, lean_box(0));
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_492_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_492_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v_a_483_);
v___x_488_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_488_, 0, v_stx_429_);
lean_ctor_set(v___x_488_, 1, v___y_472_);
lean_ctor_set(v___x_488_, 2, v___y_480_);
lean_ctor_set(v___x_488_, 3, v___y_474_);
lean_ctor_set(v___x_488_, 4, v___x_487_);
lean_ctor_set(v___x_488_, 5, v___x_470_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_488_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v___y_480_);
lean_dec(v___y_474_);
lean_dec(v___y_472_);
lean_dec(v_stx_429_);
v_a_493_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_482_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_482_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
v___jp_501_:
{
if (lean_obj_tag(v___y_503_) == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_514_, 0, v_stx_429_);
lean_ctor_set(v___x_514_, 1, v___y_502_);
lean_ctor_set(v___x_514_, 2, v___y_505_);
lean_ctor_set(v___x_514_, 3, v_partialFixpoint_x3f_506_);
lean_ctor_set(v___x_514_, 4, v___x_513_);
lean_ctor_set(v___x_514_, 5, v___x_470_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
else
{
lean_object* v_val_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_val_516_ = lean_ctor_get(v___y_503_, 0);
lean_inc(v_val_516_);
lean_dec_ref(v___y_503_);
v___x_517_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8));
lean_inc(v_val_516_);
v___x_518_ = l_Lean_Syntax_isOfKind(v_val_516_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10);
v___x_520_ = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___boxed), 10, 3);
lean_closure_set(v___x_520_, 0, lean_box(0));
lean_closure_set(v___x_520_, 1, v_val_516_);
lean_closure_set(v___x_520_, 2, v___x_519_);
v___y_472_ = v___y_502_;
v___y_473_ = v___y_508_;
v___y_474_ = v_partialFixpoint_x3f_506_;
v___y_475_ = v___y_511_;
v___y_476_ = v___y_510_;
v___y_477_ = v___y_509_;
v___y_478_ = v___y_512_;
v___y_479_ = v___y_507_;
v___y_480_ = v___y_505_;
v___y_481_ = v___x_520_;
goto v___jp_471_;
}
else
{
lean_object* v_tactic_521_; lean_object* v___x_522_; lean_object* v___f_523_; 
v_tactic_521_ = l_Lean_Syntax_getArg(v_val_516_, v___y_504_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_val_516_);
lean_ctor_set(v___x_522_, 1, v_tactic_521_);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_523_, 0, v___x_522_);
v___y_472_ = v___y_502_;
v___y_473_ = v___y_508_;
v___y_474_ = v_partialFixpoint_x3f_506_;
v___y_475_ = v___y_511_;
v___y_476_ = v___y_510_;
v___y_477_ = v___y_509_;
v___y_478_ = v___y_512_;
v___y_479_ = v___y_507_;
v___y_480_ = v___y_505_;
v___y_481_ = v___f_523_;
goto v___jp_471_;
}
}
}
v___jp_524_:
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = 0;
v___x_538_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_538_, 0, v___y_535_);
lean_ctor_set(v___x_538_, 1, v_term_x3f_536_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*2, v___x_537_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
v___y_502_ = v___y_525_;
v___y_503_ = v___y_527_;
v___y_504_ = v___y_532_;
v___y_505_ = v___y_534_;
v_partialFixpoint_x3f_506_ = v___x_539_;
v___y_507_ = v___y_526_;
v___y_508_ = v___y_533_;
v___y_509_ = v___y_529_;
v___y_510_ = v___y_531_;
v___y_511_ = v___y_530_;
v___y_512_ = v___y_528_;
goto v___jp_501_;
}
v___jp_540_:
{
uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = 1;
v___x_554_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_554_, 0, v___y_551_);
lean_ctor_set(v___x_554_, 1, v_term_x3f_552_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*2, v___x_553_);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___y_502_ = v___y_541_;
v___y_503_ = v___y_543_;
v___y_504_ = v___y_548_;
v___y_505_ = v___y_550_;
v_partialFixpoint_x3f_506_ = v___x_555_;
v___y_507_ = v___y_542_;
v___y_508_ = v___y_549_;
v___y_509_ = v___y_545_;
v___y_510_ = v___y_547_;
v___y_511_ = v___y_546_;
v___y_512_ = v___y_544_;
goto v___jp_501_;
}
v___jp_556_:
{
uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = 2;
v___x_570_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_570_, 0, v___y_567_);
lean_ctor_set(v___x_570_, 1, v_term_x3f_568_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*2, v___x_569_);
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___y_502_ = v___y_557_;
v___y_503_ = v___y_559_;
v___y_504_ = v___y_564_;
v___y_505_ = v___y_566_;
v_partialFixpoint_x3f_506_ = v___x_571_;
v___y_507_ = v___y_558_;
v___y_508_ = v___y_565_;
v___y_509_ = v___y_561_;
v___y_510_ = v___y_563_;
v___y_511_ = v___y_562_;
v___y_512_ = v___y_560_;
goto v___jp_501_;
}
v___jp_572_:
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12));
lean_inc(v_val_575_);
v___x_585_ = l_Lean_Syntax_isOfKind(v_val_575_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14));
lean_inc(v_val_575_);
v___x_587_ = l_Lean_Syntax_isOfKind(v_val_575_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16));
lean_inc(v_val_575_);
v___x_589_ = l_Lean_Syntax_isOfKind(v_val_575_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_dec(v_val_575_);
v___x_590_ = lean_box(0);
v___y_502_ = v___y_573_;
v___y_503_ = v___y_574_;
v___y_504_ = v___y_576_;
v___y_505_ = v_terminationBy_x3f_577_;
v_partialFixpoint_x3f_506_ = v___x_590_;
v___y_507_ = v___y_578_;
v___y_508_ = v___y_579_;
v___y_509_ = v___y_580_;
v___y_510_ = v___y_581_;
v___y_511_ = v___y_582_;
v___y_512_ = v___y_583_;
goto v___jp_501_;
}
else
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = l_Lean_Syntax_getArg(v_val_575_, v___y_576_);
v___x_592_ = l_Lean_Syntax_isNone(v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_591_);
v___x_594_ = l_Lean_Syntax_matchesNull(v___x_591_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
lean_dec(v___x_591_);
lean_dec(v_val_575_);
v___x_595_ = lean_box(0);
v___y_502_ = v___y_573_;
v___y_503_ = v___y_574_;
v___y_504_ = v___y_576_;
v___y_505_ = v_terminationBy_x3f_577_;
v_partialFixpoint_x3f_506_ = v___x_595_;
v___y_507_ = v___y_578_;
v___y_508_ = v___y_579_;
v___y_509_ = v___y_580_;
v___y_510_ = v___y_581_;
v___y_511_ = v___y_582_;
v___y_512_ = v___y_583_;
goto v___jp_501_;
}
else
{
lean_object* v_term_x3f_596_; lean_object* v___x_597_; 
v_term_x3f_596_ = l_Lean_Syntax_getArg(v___x_591_, v___y_576_);
lean_dec(v___x_591_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_term_x3f_596_);
v___y_557_ = v___y_573_;
v___y_558_ = v___y_578_;
v___y_559_ = v___y_574_;
v___y_560_ = v___y_583_;
v___y_561_ = v___y_580_;
v___y_562_ = v___y_582_;
v___y_563_ = v___y_581_;
v___y_564_ = v___y_576_;
v___y_565_ = v___y_579_;
v___y_566_ = v_terminationBy_x3f_577_;
v___y_567_ = v_val_575_;
v_term_x3f_568_ = v___x_597_;
goto v___jp_556_;
}
}
else
{
lean_object* v___x_598_; 
lean_dec(v___x_591_);
v___x_598_ = lean_box(0);
v___y_557_ = v___y_573_;
v___y_558_ = v___y_578_;
v___y_559_ = v___y_574_;
v___y_560_ = v___y_583_;
v___y_561_ = v___y_580_;
v___y_562_ = v___y_582_;
v___y_563_ = v___y_581_;
v___y_564_ = v___y_576_;
v___y_565_ = v___y_579_;
v___y_566_ = v_terminationBy_x3f_577_;
v___y_567_ = v_val_575_;
v_term_x3f_568_ = v___x_598_;
goto v___jp_556_;
}
}
}
else
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = l_Lean_Syntax_getArg(v_val_575_, v___y_576_);
v___x_600_ = l_Lean_Syntax_isNone(v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_599_);
v___x_602_ = l_Lean_Syntax_matchesNull(v___x_599_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
lean_dec(v___x_599_);
lean_dec(v_val_575_);
v___x_603_ = lean_box(0);
v___y_502_ = v___y_573_;
v___y_503_ = v___y_574_;
v___y_504_ = v___y_576_;
v___y_505_ = v_terminationBy_x3f_577_;
v_partialFixpoint_x3f_506_ = v___x_603_;
v___y_507_ = v___y_578_;
v___y_508_ = v___y_579_;
v___y_509_ = v___y_580_;
v___y_510_ = v___y_581_;
v___y_511_ = v___y_582_;
v___y_512_ = v___y_583_;
goto v___jp_501_;
}
else
{
lean_object* v_term_x3f_604_; lean_object* v___x_605_; 
v_term_x3f_604_ = l_Lean_Syntax_getArg(v___x_599_, v___y_576_);
lean_dec(v___x_599_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v_term_x3f_604_);
v___y_541_ = v___y_573_;
v___y_542_ = v___y_578_;
v___y_543_ = v___y_574_;
v___y_544_ = v___y_583_;
v___y_545_ = v___y_580_;
v___y_546_ = v___y_582_;
v___y_547_ = v___y_581_;
v___y_548_ = v___y_576_;
v___y_549_ = v___y_579_;
v___y_550_ = v_terminationBy_x3f_577_;
v___y_551_ = v_val_575_;
v_term_x3f_552_ = v___x_605_;
goto v___jp_540_;
}
}
else
{
lean_object* v___x_606_; 
lean_dec(v___x_599_);
v___x_606_ = lean_box(0);
v___y_541_ = v___y_573_;
v___y_542_ = v___y_578_;
v___y_543_ = v___y_574_;
v___y_544_ = v___y_583_;
v___y_545_ = v___y_580_;
v___y_546_ = v___y_582_;
v___y_547_ = v___y_581_;
v___y_548_ = v___y_576_;
v___y_549_ = v___y_579_;
v___y_550_ = v_terminationBy_x3f_577_;
v___y_551_ = v_val_575_;
v_term_x3f_552_ = v___x_606_;
goto v___jp_540_;
}
}
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = l_Lean_Syntax_getArg(v_val_575_, v___y_576_);
v___x_608_ = l_Lean_Syntax_isNone(v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_607_);
v___x_610_ = l_Lean_Syntax_matchesNull(v___x_607_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
lean_dec(v___x_607_);
lean_dec(v_val_575_);
v___x_611_ = lean_box(0);
v___y_502_ = v___y_573_;
v___y_503_ = v___y_574_;
v___y_504_ = v___y_576_;
v___y_505_ = v_terminationBy_x3f_577_;
v_partialFixpoint_x3f_506_ = v___x_611_;
v___y_507_ = v___y_578_;
v___y_508_ = v___y_579_;
v___y_509_ = v___y_580_;
v___y_510_ = v___y_581_;
v___y_511_ = v___y_582_;
v___y_512_ = v___y_583_;
goto v___jp_501_;
}
else
{
lean_object* v_term_x3f_612_; lean_object* v___x_613_; 
v_term_x3f_612_ = l_Lean_Syntax_getArg(v___x_607_, v___y_576_);
lean_dec(v___x_607_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_term_x3f_612_);
v___y_525_ = v___y_573_;
v___y_526_ = v___y_578_;
v___y_527_ = v___y_574_;
v___y_528_ = v___y_583_;
v___y_529_ = v___y_580_;
v___y_530_ = v___y_582_;
v___y_531_ = v___y_581_;
v___y_532_ = v___y_576_;
v___y_533_ = v___y_579_;
v___y_534_ = v_terminationBy_x3f_577_;
v___y_535_ = v_val_575_;
v_term_x3f_536_ = v___x_613_;
goto v___jp_524_;
}
}
else
{
lean_object* v___x_614_; 
lean_dec(v___x_607_);
v___x_614_ = lean_box(0);
v___y_525_ = v___y_573_;
v___y_526_ = v___y_578_;
v___y_527_ = v___y_574_;
v___y_528_ = v___y_583_;
v___y_529_ = v___y_580_;
v___y_530_ = v___y_582_;
v___y_531_ = v___y_581_;
v___y_532_ = v___y_576_;
v___y_533_ = v___y_579_;
v___y_534_ = v_terminationBy_x3f_577_;
v___y_535_ = v_val_575_;
v_term_x3f_536_ = v___x_614_;
goto v___jp_524_;
}
}
}
v___jp_615_:
{
if (lean_obj_tag(v___y_618_) == 1)
{
lean_object* v_val_627_; 
v_val_627_ = lean_ctor_get(v___y_618_, 0);
lean_inc(v_val_627_);
lean_dec_ref(v___y_618_);
v___y_573_ = v___y_616_;
v___y_574_ = v___y_617_;
v_val_575_ = v_val_627_;
v___y_576_ = v___y_619_;
v_terminationBy_x3f_577_ = v_terminationBy_x3f_620_;
v___y_578_ = v___y_621_;
v___y_579_ = v___y_622_;
v___y_580_ = v___y_623_;
v___y_581_ = v___y_624_;
v___y_582_ = v___y_625_;
v___y_583_ = v___y_626_;
goto v___jp_572_;
}
else
{
lean_object* v___x_628_; 
lean_dec(v___y_618_);
v___x_628_ = lean_box(0);
v___y_502_ = v___y_616_;
v___y_503_ = v___y_617_;
v___y_504_ = v___y_619_;
v___y_505_ = v_terminationBy_x3f_620_;
v_partialFixpoint_x3f_506_ = v___x_628_;
v___y_507_ = v___y_621_;
v___y_508_ = v___y_622_;
v___y_509_ = v___y_623_;
v___y_510_ = v___y_624_;
v___y_511_ = v___y_625_;
v___y_512_ = v___y_626_;
goto v___jp_501_;
}
}
v___jp_629_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__17));
v___x_645_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_645_, 0, v___y_636_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_ctor_set(v___x_645_, 2, v___y_633_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*3, v___y_643_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*3 + 1, v___y_639_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___y_616_ = v___y_630_;
v___y_617_ = v___y_631_;
v___y_618_ = v___y_634_;
v___y_619_ = v___y_635_;
v_terminationBy_x3f_620_ = v___x_646_;
v___y_621_ = v___y_641_;
v___y_622_ = v___y_637_;
v___y_623_ = v___y_642_;
v___y_624_ = v___y_632_;
v___y_625_ = v___y_638_;
v___y_626_ = v___y_640_;
goto v___jp_615_;
}
v___jp_647_:
{
lean_object* v___x_658_; 
v___x_658_ = lean_box(0);
v___y_616_ = v___y_648_;
v___y_617_ = v___y_649_;
v___y_618_ = v___y_651_;
v___y_619_ = v___y_652_;
v_terminationBy_x3f_620_ = v___x_658_;
v___y_621_ = v___y_655_;
v___y_622_ = v___y_657_;
v___y_623_ = v___y_654_;
v___y_624_ = v___y_650_;
v___y_625_ = v___y_656_;
v___y_626_ = v___y_653_;
goto v___jp_615_;
}
v___jp_659_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_box(0);
v___y_616_ = v___y_660_;
v___y_617_ = v___y_661_;
v___y_618_ = v___y_663_;
v___y_619_ = v___y_664_;
v_terminationBy_x3f_620_ = v___x_670_;
v___y_621_ = v___y_667_;
v___y_622_ = v___y_669_;
v___y_623_ = v___y_666_;
v___y_624_ = v___y_662_;
v___y_625_ = v___y_668_;
v___y_626_ = v___y_665_;
goto v___jp_615_;
}
v___jp_671_:
{
lean_object* v___x_682_; 
v___x_682_ = lean_box(0);
v___y_616_ = v___y_672_;
v___y_617_ = v___y_673_;
v___y_618_ = v___y_675_;
v___y_619_ = v___y_676_;
v_terminationBy_x3f_620_ = v___x_682_;
v___y_621_ = v___y_679_;
v___y_622_ = v___y_681_;
v___y_623_ = v___y_678_;
v___y_624_ = v___y_674_;
v___y_625_ = v___y_680_;
v___y_626_ = v___y_677_;
goto v___jp_615_;
}
v___jp_683_:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_699_, 0, v___y_692_);
lean_ctor_set(v___x_699_, 1, v___y_686_);
lean_ctor_set(v___x_699_, 2, v___y_684_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*3, v___y_698_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*3 + 1, v___y_688_);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
v___y_616_ = v___y_685_;
v___y_617_ = v___y_687_;
v___y_618_ = v___y_690_;
v___y_619_ = v___y_691_;
v_terminationBy_x3f_620_ = v___x_700_;
v___y_621_ = v___y_696_;
v___y_622_ = v___y_693_;
v___y_623_ = v___y_697_;
v___y_624_ = v___y_689_;
v___y_625_ = v___y_694_;
v___y_626_ = v___y_695_;
goto v___jp_615_;
}
v___jp_701_:
{
lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_714_ = lean_unsigned_to_nat(2u);
v___x_715_ = l_Lean_Syntax_getArg(v___y_707_, v___x_714_);
lean_inc(v___x_715_);
v___x_716_ = l_Lean_Syntax_matchesNull(v___x_715_, v___x_714_);
if (v___x_716_ == 0)
{
uint8_t v___x_717_; 
v___x_717_ = l_Lean_Syntax_matchesNull(v___x_715_, v___x_470_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_s_713_);
lean_dec(v___y_705_);
lean_dec(v___y_703_);
lean_dec(v___y_702_);
lean_dec(v_stx_429_);
v___x_718_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_719_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___y_707_, v___x_718_, v___y_710_, v___y_712_, v___y_709_, v___y_704_, v___y_711_, v___y_708_);
lean_dec(v___y_708_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_712_);
lean_dec(v___y_707_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v___x_728_; lean_object* v_body_729_; 
v___x_728_ = lean_unsigned_to_nat(3u);
v_body_729_ = l_Lean_Syntax_getArg(v___y_707_, v___x_728_);
if (lean_obj_tag(v_s_713_) == 0)
{
v___y_630_ = v___y_702_;
v___y_631_ = v___y_703_;
v___y_632_ = v___y_704_;
v___y_633_ = v_body_729_;
v___y_634_ = v___y_705_;
v___y_635_ = v___y_706_;
v___y_636_ = v___y_707_;
v___y_637_ = v___y_712_;
v___y_638_ = v___y_711_;
v___y_639_ = v___x_716_;
v___y_640_ = v___y_708_;
v___y_641_ = v___y_710_;
v___y_642_ = v___y_709_;
v___y_643_ = v___x_716_;
goto v___jp_629_;
}
else
{
lean_dec_ref(v_s_713_);
v___y_630_ = v___y_702_;
v___y_631_ = v___y_703_;
v___y_632_ = v___y_704_;
v___y_633_ = v_body_729_;
v___y_634_ = v___y_705_;
v___y_635_ = v___y_706_;
v___y_636_ = v___y_707_;
v___y_637_ = v___y_712_;
v___y_638_ = v___y_711_;
v___y_639_ = v___x_716_;
v___y_640_ = v___y_708_;
v___y_641_ = v___y_710_;
v___y_642_ = v___y_709_;
v___y_643_ = v___x_717_;
goto v___jp_629_;
}
}
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = l_Lean_Syntax_getArg(v___x_715_, v___x_470_);
lean_dec(v___x_715_);
lean_inc(v___x_730_);
v___x_731_ = l_Lean_Syntax_matchesNull(v___x_730_, v___x_470_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v_body_733_; lean_object* v_vars_734_; 
v___x_732_ = lean_unsigned_to_nat(3u);
v_body_733_ = l_Lean_Syntax_getArg(v___y_707_, v___x_732_);
v_vars_734_ = l_Lean_Syntax_getArgs(v___x_730_);
lean_dec(v___x_730_);
if (lean_obj_tag(v_s_713_) == 0)
{
v___y_684_ = v_body_733_;
v___y_685_ = v___y_702_;
v___y_686_ = v_vars_734_;
v___y_687_ = v___y_703_;
v___y_688_ = v___x_731_;
v___y_689_ = v___y_704_;
v___y_690_ = v___y_705_;
v___y_691_ = v___y_706_;
v___y_692_ = v___y_707_;
v___y_693_ = v___y_712_;
v___y_694_ = v___y_711_;
v___y_695_ = v___y_708_;
v___y_696_ = v___y_710_;
v___y_697_ = v___y_709_;
v___y_698_ = v___x_731_;
goto v___jp_683_;
}
else
{
lean_dec_ref(v_s_713_);
v___y_684_ = v_body_733_;
v___y_685_ = v___y_702_;
v___y_686_ = v_vars_734_;
v___y_687_ = v___y_703_;
v___y_688_ = v___x_731_;
v___y_689_ = v___y_704_;
v___y_690_ = v___y_705_;
v___y_691_ = v___y_706_;
v___y_692_ = v___y_707_;
v___y_693_ = v___y_712_;
v___y_694_ = v___y_711_;
v___y_695_ = v___y_708_;
v___y_696_ = v___y_710_;
v___y_697_ = v___y_709_;
v___y_698_ = v___x_716_;
goto v___jp_683_;
}
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v___x_730_);
lean_dec(v_s_713_);
lean_dec(v___y_705_);
lean_dec(v___y_703_);
lean_dec(v___y_702_);
lean_dec(v_stx_429_);
v___x_735_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21);
v___x_736_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___y_707_, v___x_735_, v___y_710_, v___y_712_, v___y_709_, v___y_704_, v___y_711_, v___y_708_);
lean_dec(v___y_708_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_712_);
lean_dec(v___y_707_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
v___jp_745_:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23));
lean_inc(v_val_748_);
v___x_758_ = l_Lean_Syntax_isOfKind(v_val_748_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25));
lean_inc(v_val_748_);
v___x_760_ = l_Lean_Syntax_isOfKind(v_val_748_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12));
lean_inc(v_val_748_);
v___x_762_ = l_Lean_Syntax_isOfKind(v_val_748_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14));
lean_inc(v_val_748_);
v___x_764_ = l_Lean_Syntax_isOfKind(v_val_748_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16));
lean_inc(v_val_748_);
v___x_766_ = l_Lean_Syntax_isOfKind(v_val_748_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec(v_terminationBy_x3f_x3f_750_);
lean_dec(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v_stx_429_);
v___x_767_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_768_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_748_, v___x_767_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v_val_748_);
v_a_769_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_768_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = l_Lean_Syntax_getArg(v_val_748_, v___y_749_);
v___x_778_ = l_Lean_Syntax_isNone(v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(2u);
v___x_780_ = l_Lean_Syntax_matchesNull(v___x_777_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_terminationBy_x3f_x3f_750_);
lean_dec(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v_stx_429_);
v___x_781_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_782_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_748_, v___x_781_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v_val_748_);
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
else
{
lean_dec(v_val_748_);
v___y_672_ = v_terminationBy_x3f_x3f_750_;
v___y_673_ = v___y_746_;
v___y_674_ = v___y_754_;
v___y_675_ = v___y_747_;
v___y_676_ = v___y_749_;
v___y_677_ = v___y_756_;
v___y_678_ = v___y_753_;
v___y_679_ = v___y_751_;
v___y_680_ = v___y_755_;
v___y_681_ = v___y_752_;
goto v___jp_671_;
}
}
else
{
lean_dec(v___x_777_);
lean_dec(v_val_748_);
v___y_672_ = v_terminationBy_x3f_x3f_750_;
v___y_673_ = v___y_746_;
v___y_674_ = v___y_754_;
v___y_675_ = v___y_747_;
v___y_676_ = v___y_749_;
v___y_677_ = v___y_756_;
v___y_678_ = v___y_753_;
v___y_679_ = v___y_751_;
v___y_680_ = v___y_755_;
v___y_681_ = v___y_752_;
goto v___jp_671_;
}
}
}
else
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = l_Lean_Syntax_getArg(v_val_748_, v___y_749_);
v___x_792_ = l_Lean_Syntax_isNone(v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(2u);
v___x_794_ = l_Lean_Syntax_matchesNull(v___x_791_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_terminationBy_x3f_x3f_750_);
lean_dec(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v_stx_429_);
v___x_795_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_796_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_748_, v___x_795_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v_val_748_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
else
{
lean_dec(v_val_748_);
v___y_660_ = v_terminationBy_x3f_x3f_750_;
v___y_661_ = v___y_746_;
v___y_662_ = v___y_754_;
v___y_663_ = v___y_747_;
v___y_664_ = v___y_749_;
v___y_665_ = v___y_756_;
v___y_666_ = v___y_753_;
v___y_667_ = v___y_751_;
v___y_668_ = v___y_755_;
v___y_669_ = v___y_752_;
goto v___jp_659_;
}
}
else
{
lean_dec(v___x_791_);
lean_dec(v_val_748_);
v___y_660_ = v_terminationBy_x3f_x3f_750_;
v___y_661_ = v___y_746_;
v___y_662_ = v___y_754_;
v___y_663_ = v___y_747_;
v___y_664_ = v___y_749_;
v___y_665_ = v___y_756_;
v___y_666_ = v___y_753_;
v___y_667_ = v___y_751_;
v___y_668_ = v___y_755_;
v___y_669_ = v___y_752_;
goto v___jp_659_;
}
}
}
else
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = l_Lean_Syntax_getArg(v_val_748_, v___y_749_);
v___x_806_ = l_Lean_Syntax_isNone(v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(2u);
v___x_808_ = l_Lean_Syntax_matchesNull(v___x_805_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_terminationBy_x3f_x3f_750_);
lean_dec(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v_stx_429_);
v___x_809_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_810_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_748_, v___x_809_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v_val_748_);
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
lean_dec(v_val_748_);
v___y_648_ = v_terminationBy_x3f_x3f_750_;
v___y_649_ = v___y_746_;
v___y_650_ = v___y_754_;
v___y_651_ = v___y_747_;
v___y_652_ = v___y_749_;
v___y_653_ = v___y_756_;
v___y_654_ = v___y_753_;
v___y_655_ = v___y_751_;
v___y_656_ = v___y_755_;
v___y_657_ = v___y_752_;
goto v___jp_647_;
}
}
else
{
lean_dec(v___x_805_);
lean_dec(v_val_748_);
v___y_648_ = v_terminationBy_x3f_x3f_750_;
v___y_649_ = v___y_746_;
v___y_650_ = v___y_754_;
v___y_651_ = v___y_747_;
v___y_652_ = v___y_749_;
v___y_653_ = v___y_756_;
v___y_654_ = v___y_753_;
v___y_655_ = v___y_751_;
v___y_656_ = v___y_755_;
v___y_657_ = v___y_752_;
goto v___jp_647_;
}
}
}
else
{
lean_object* v___x_819_; 
lean_dec(v___y_747_);
v___x_819_ = lean_box(0);
v___y_573_ = v_terminationBy_x3f_x3f_750_;
v___y_574_ = v___y_746_;
v_val_575_ = v_val_748_;
v___y_576_ = v___y_749_;
v_terminationBy_x3f_577_ = v___x_819_;
v___y_578_ = v___y_751_;
v___y_579_ = v___y_752_;
v___y_580_ = v___y_753_;
v___y_581_ = v___y_754_;
v___y_582_ = v___y_755_;
v___y_583_ = v___y_756_;
goto v___jp_572_;
}
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_820_ = l_Lean_Syntax_getArg(v_val_748_, v___y_749_);
v___x_821_ = l_Lean_Syntax_isNone(v___x_820_);
if (v___x_821_ == 0)
{
uint8_t v___x_822_; 
lean_inc(v___x_820_);
v___x_822_ = l_Lean_Syntax_matchesNull(v___x_820_, v___y_749_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v___x_820_);
lean_dec(v_terminationBy_x3f_x3f_750_);
lean_dec(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v_stx_429_);
v___x_823_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_824_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_748_, v___x_823_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec(v_val_748_);
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
else
{
lean_object* v_s_833_; lean_object* v___x_834_; 
v_s_833_ = l_Lean_Syntax_getArg(v___x_820_, v___x_470_);
lean_dec(v___x_820_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v_s_833_);
v___y_702_ = v_terminationBy_x3f_x3f_750_;
v___y_703_ = v___y_746_;
v___y_704_ = v___y_754_;
v___y_705_ = v___y_747_;
v___y_706_ = v___y_749_;
v___y_707_ = v_val_748_;
v___y_708_ = v___y_756_;
v___y_709_ = v___y_753_;
v___y_710_ = v___y_751_;
v___y_711_ = v___y_755_;
v___y_712_ = v___y_752_;
v_s_713_ = v___x_834_;
goto v___jp_701_;
}
}
else
{
lean_object* v___x_835_; 
lean_dec(v___x_820_);
v___x_835_ = lean_box(0);
v___y_702_ = v_terminationBy_x3f_x3f_750_;
v___y_703_ = v___y_746_;
v___y_704_ = v___y_754_;
v___y_705_ = v___y_747_;
v___y_706_ = v___y_749_;
v___y_707_ = v_val_748_;
v___y_708_ = v___y_756_;
v___y_709_ = v___y_753_;
v___y_710_ = v___y_751_;
v___y_711_ = v___y_755_;
v___y_712_ = v___y_752_;
v_s_713_ = v___x_835_;
goto v___jp_701_;
}
}
}
v___jp_836_:
{
if (lean_obj_tag(v___y_837_) == 1)
{
lean_object* v_val_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_val_840_ = lean_ctor_get(v___y_837_, 0);
lean_inc(v_val_840_);
v___x_841_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25));
lean_inc(v_val_840_);
v___x_842_ = l_Lean_Syntax_isOfKind(v_val_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
v___x_843_ = lean_box(0);
v___y_746_ = v_d_x3f_839_;
v___y_747_ = v___y_837_;
v_val_748_ = v_val_840_;
v___y_749_ = v___y_838_;
v_terminationBy_x3f_x3f_750_ = v___x_843_;
v___y_751_ = v___y_430_;
v___y_752_ = v___y_431_;
v___y_753_ = v___y_432_;
v___y_754_ = v___y_433_;
v___y_755_ = v___y_434_;
v___y_756_ = v___y_435_;
goto v___jp_745_;
}
else
{
lean_object* v___x_844_; 
lean_inc(v_val_840_);
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v_val_840_);
v___y_746_ = v_d_x3f_839_;
v___y_747_ = v___y_837_;
v_val_748_ = v_val_840_;
v___y_749_ = v___y_838_;
v_terminationBy_x3f_x3f_750_ = v___x_844_;
v___y_751_ = v___y_430_;
v___y_752_ = v___y_431_;
v___y_753_ = v___y_432_;
v___y_754_ = v___y_433_;
v___y_755_ = v___y_434_;
v___y_756_ = v___y_435_;
goto v___jp_745_;
}
}
else
{
lean_object* v___x_845_; 
v___x_845_ = lean_box(0);
if (lean_obj_tag(v___y_837_) == 1)
{
lean_object* v_val_846_; 
v_val_846_ = lean_ctor_get(v___y_837_, 0);
lean_inc(v_val_846_);
v___y_746_ = v_d_x3f_839_;
v___y_747_ = v___y_837_;
v_val_748_ = v_val_846_;
v___y_749_ = v___y_838_;
v_terminationBy_x3f_x3f_750_ = v___x_845_;
v___y_751_ = v___y_430_;
v___y_752_ = v___y_431_;
v___y_753_ = v___y_432_;
v___y_754_ = v___y_433_;
v___y_755_ = v___y_434_;
v___y_756_ = v___y_435_;
goto v___jp_745_;
}
else
{
v___y_616_ = v___x_845_;
v___y_617_ = v_d_x3f_839_;
v___y_618_ = v___y_837_;
v___y_619_ = v___y_838_;
v_terminationBy_x3f_620_ = v___x_845_;
v___y_621_ = v___y_430_;
v___y_622_ = v___y_431_;
v___y_623_ = v___y_432_;
v___y_624_ = v___y_433_;
v___y_625_ = v___y_434_;
v___y_626_ = v___y_435_;
goto v___jp_615_;
}
}
}
v___jp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = l_Lean_Syntax_getArg(v_stx_429_, v___x_849_);
v___x_851_ = l_Lean_Syntax_isNone(v___x_850_);
if (v___x_851_ == 0)
{
uint8_t v___x_852_; 
lean_inc(v___x_850_);
v___x_852_ = l_Lean_Syntax_matchesNull(v___x_850_, v___x_849_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
lean_dec(v___x_850_);
lean_dec(v_t_x3f_848_);
v___x_853_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_854_ = lean_box(0);
lean_inc(v_stx_429_);
v___x_855_ = l_Lean_Syntax_formatStx(v_stx_429_, v___x_854_, v___x_852_);
v___x_856_ = l_Std_Format_defWidth;
v___x_857_ = l_Std_Format_pretty(v___x_855_, v___x_856_, v___x_470_, v___x_470_);
v___x_858_ = lean_string_append(v___x_853_, v___x_857_);
lean_dec_ref(v___x_857_);
v___x_859_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_860_ = lean_string_append(v___x_858_, v___x_859_);
lean_inc(v_stx_429_);
v___x_861_ = l_Lean_Syntax_getKind(v_stx_429_);
v___x_862_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_861_, v___x_453_);
v___x_863_ = lean_string_append(v___x_860_, v___x_862_);
lean_dec_ref(v___x_862_);
v___x_864_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
v___x_865_ = l_Lean_MessageData_ofFormat(v___x_864_);
v___x_866_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_429_, v___x_865_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec(v_stx_429_);
return v___x_866_;
}
else
{
lean_object* v_d_x3f_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_d_x3f_867_ = l_Lean_Syntax_getArg(v___x_850_, v___x_470_);
lean_dec(v___x_850_);
v___x_868_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8));
lean_inc(v_d_x3f_867_);
v___x_869_ = l_Lean_Syntax_isOfKind(v_d_x3f_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
lean_dec(v_d_x3f_867_);
lean_dec(v_t_x3f_848_);
v___x_870_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_871_ = lean_box(0);
lean_inc(v_stx_429_);
v___x_872_ = l_Lean_Syntax_formatStx(v_stx_429_, v___x_871_, v___x_869_);
v___x_873_ = l_Std_Format_defWidth;
v___x_874_ = l_Std_Format_pretty(v___x_872_, v___x_873_, v___x_470_, v___x_470_);
v___x_875_ = lean_string_append(v___x_870_, v___x_874_);
lean_dec_ref(v___x_874_);
v___x_876_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_877_ = lean_string_append(v___x_875_, v___x_876_);
lean_inc(v_stx_429_);
v___x_878_ = l_Lean_Syntax_getKind(v_stx_429_);
v___x_879_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_878_, v___x_852_);
v___x_880_ = lean_string_append(v___x_877_, v___x_879_);
lean_dec_ref(v___x_879_);
v___x_881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
v___x_882_ = l_Lean_MessageData_ofFormat(v___x_881_);
v___x_883_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_429_, v___x_882_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec(v_stx_429_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; 
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v_d_x3f_867_);
v___y_837_ = v_t_x3f_848_;
v___y_838_ = v___x_849_;
v_d_x3f_839_ = v___x_884_;
goto v___jp_836_;
}
}
}
else
{
lean_object* v___x_885_; 
lean_dec(v___x_850_);
v___x_885_ = lean_box(0);
v___y_837_ = v_t_x3f_848_;
v___y_838_ = v___x_849_;
v_d_x3f_839_ = v___x_885_;
goto v___jp_836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___boxed(lean_object* v_stx_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(v_stx_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
return v_res_915_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_916_; double v___x_917_; 
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_float_of_nat(v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(lean_object* v_cls_921_, lean_object* v_msg_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_ref_928_; lean_object* v___x_929_; lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_974_; 
v_ref_928_ = lean_ctor_get(v___y_925_, 5);
v___x_929_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(v_msg_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_974_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_974_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_974_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v_traceState_935_; lean_object* v_env_936_; lean_object* v_nextMacroScope_937_; lean_object* v_ngen_938_; lean_object* v_auxDeclNGen_939_; lean_object* v_cache_940_; lean_object* v_messages_941_; lean_object* v_infoState_942_; lean_object* v_snapshotTasks_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_973_; 
v___x_934_ = lean_st_ref_take(v___y_926_);
v_traceState_935_ = lean_ctor_get(v___x_934_, 4);
v_env_936_ = lean_ctor_get(v___x_934_, 0);
v_nextMacroScope_937_ = lean_ctor_get(v___x_934_, 1);
v_ngen_938_ = lean_ctor_get(v___x_934_, 2);
v_auxDeclNGen_939_ = lean_ctor_get(v___x_934_, 3);
v_cache_940_ = lean_ctor_get(v___x_934_, 5);
v_messages_941_ = lean_ctor_get(v___x_934_, 6);
v_infoState_942_ = lean_ctor_get(v___x_934_, 7);
v_snapshotTasks_943_ = lean_ctor_get(v___x_934_, 8);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_973_ == 0)
{
v___x_945_ = v___x_934_;
v_isShared_946_ = v_isSharedCheck_973_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_snapshotTasks_943_);
lean_inc(v_infoState_942_);
lean_inc(v_messages_941_);
lean_inc(v_cache_940_);
lean_inc(v_traceState_935_);
lean_inc(v_auxDeclNGen_939_);
lean_inc(v_ngen_938_);
lean_inc(v_nextMacroScope_937_);
lean_inc(v_env_936_);
lean_dec(v___x_934_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_973_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
uint64_t v_tid_947_; lean_object* v_traces_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_972_; 
v_tid_947_ = lean_ctor_get_uint64(v_traceState_935_, sizeof(void*)*1);
v_traces_948_ = lean_ctor_get(v_traceState_935_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v_traceState_935_);
if (v_isSharedCheck_972_ == 0)
{
v___x_950_ = v_traceState_935_;
v_isShared_951_ = v_isSharedCheck_972_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_traces_948_);
lean_dec(v_traceState_935_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_972_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; double v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_952_ = lean_box(0);
v___x_953_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__0);
v___x_954_ = 0;
v___x_955_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__1));
v___x_956_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_956_, 0, v_cls_921_);
lean_ctor_set(v___x_956_, 1, v___x_952_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
lean_ctor_set_float(v___x_956_, sizeof(void*)*3, v___x_953_);
lean_ctor_set_float(v___x_956_, sizeof(void*)*3 + 8, v___x_953_);
lean_ctor_set_uint8(v___x_956_, sizeof(void*)*3 + 16, v___x_954_);
v___x_957_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__2));
v___x_958_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v_a_930_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
lean_inc(v_ref_928_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v_ref_928_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Lean_PersistentArray_push___redArg(v_traces_948_, v___x_959_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_960_);
v___x_962_ = v___x_950_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_960_);
lean_ctor_set_uint64(v_reuseFailAlloc_971_, sizeof(void*)*1, v_tid_947_);
v___x_962_ = v_reuseFailAlloc_971_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 4, v___x_962_);
v___x_964_ = v___x_945_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_env_936_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_nextMacroScope_937_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_ngen_938_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_auxDeclNGen_939_);
lean_ctor_set(v_reuseFailAlloc_970_, 4, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_970_, 5, v_cache_940_);
lean_ctor_set(v_reuseFailAlloc_970_, 6, v_messages_941_);
lean_ctor_set(v_reuseFailAlloc_970_, 7, v_infoState_942_);
lean_ctor_set(v_reuseFailAlloc_970_, 8, v_snapshotTasks_943_);
v___x_964_ = v_reuseFailAlloc_970_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_965_ = lean_st_ref_set(v___y_926_, v___x_964_);
v___x_966_ = lean_box(0);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_966_);
v___x_968_ = v___x_932_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___boxed(lean_object* v_cls_975_, lean_object* v_msg_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_cls_975_, v_msg_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_982_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41___redArg(lean_object* v_keys_983_, lean_object* v_i_984_, lean_object* v_k_985_){
_start:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_array_get_size(v_keys_983_);
v___x_987_ = lean_nat_dec_lt(v_i_984_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec(v_i_984_);
return v___x_987_;
}
else
{
lean_object* v_k_x27_988_; uint8_t v___x_989_; 
v_k_x27_988_ = lean_array_fget_borrowed(v_keys_983_, v_i_984_);
v___x_989_ = l_Lean_instBEqExtraModUse_beq(v_k_985_, v_k_x27_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_add(v_i_984_, v___x_990_);
lean_dec(v_i_984_);
v_i_984_ = v___x_991_;
goto _start;
}
else
{
lean_dec(v_i_984_);
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41___redArg___boxed(lean_object* v_keys_993_, lean_object* v_i_994_, lean_object* v_k_995_){
_start:
{
uint8_t v_res_996_; lean_object* v_r_997_; 
v_res_996_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41___redArg(v_keys_993_, v_i_994_, v_k_995_);
lean_dec_ref(v_k_995_);
lean_dec_ref(v_keys_993_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__0(void){
_start:
{
size_t v___x_998_; size_t v___x_999_; size_t v___x_1000_; 
v___x_998_ = ((size_t)5ULL);
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_shift_left(v___x_999_, v___x_998_);
return v___x_1000_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__1(void){
_start:
{
size_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; 
v___x_1001_ = ((size_t)1ULL);
v___x_1002_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__0);
v___x_1003_ = lean_usize_sub(v___x_1002_, v___x_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg(lean_object* v_x_1004_, size_t v_x_1005_, lean_object* v_x_1006_){
_start:
{
if (lean_obj_tag(v_x_1004_) == 0)
{
lean_object* v_es_1007_; lean_object* v___x_1008_; size_t v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; lean_object* v_j_1012_; lean_object* v___x_1013_; 
v_es_1007_ = lean_ctor_get(v_x_1004_, 0);
lean_inc_ref(v_es_1007_);
lean_dec_ref(v_x_1004_);
v___x_1008_ = lean_box(2);
v___x_1009_ = ((size_t)5ULL);
v___x_1010_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___closed__1);
v___x_1011_ = lean_usize_land(v_x_1005_, v___x_1010_);
v_j_1012_ = lean_usize_to_nat(v___x_1011_);
v___x_1013_ = lean_array_get(v___x_1008_, v_es_1007_, v_j_1012_);
lean_dec(v_j_1012_);
lean_dec_ref(v_es_1007_);
switch(lean_obj_tag(v___x_1013_))
{
case 0:
{
lean_object* v_key_1014_; uint8_t v___x_1015_; 
v_key_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_key_1014_);
lean_dec_ref(v___x_1013_);
v___x_1015_ = l_Lean_instBEqExtraModUse_beq(v_x_1006_, v_key_1014_);
lean_dec(v_key_1014_);
return v___x_1015_;
}
case 1:
{
lean_object* v_node_1016_; size_t v___x_1017_; 
v_node_1016_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_node_1016_);
lean_dec_ref(v___x_1013_);
v___x_1017_ = lean_usize_shift_right(v_x_1005_, v___x_1009_);
v_x_1004_ = v_node_1016_;
v_x_1005_ = v___x_1017_;
goto _start;
}
default: 
{
uint8_t v___x_1019_; 
v___x_1019_ = 0;
return v___x_1019_;
}
}
}
else
{
lean_object* v_ks_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_ks_1020_ = lean_ctor_get(v_x_1004_, 0);
lean_inc_ref(v_ks_1020_);
lean_dec_ref(v_x_1004_);
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41___redArg(v_ks_1020_, v___x_1021_, v_x_1006_);
lean_dec_ref(v_ks_1020_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg___boxed(lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
size_t v_x_54468__boxed_1026_; uint8_t v_res_1027_; lean_object* v_r_1028_; 
v_x_54468__boxed_1026_ = lean_unbox_usize(v_x_1024_);
lean_dec(v_x_1024_);
v_res_1027_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg(v_x_1023_, v_x_54468__boxed_1026_, v_x_1025_);
lean_dec_ref(v_x_1025_);
v_r_1028_ = lean_box(v_res_1027_);
return v_r_1028_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27___redArg(lean_object* v_x_1029_, lean_object* v_x_1030_){
_start:
{
uint64_t v___x_1031_; size_t v___x_1032_; uint8_t v___x_1033_; 
v___x_1031_ = l_Lean_instHashableExtraModUse_hash(v_x_1030_);
v___x_1032_ = lean_uint64_to_usize(v___x_1031_);
v___x_1033_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg(v_x_1029_, v___x_1032_, v_x_1030_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27___redArg___boxed(lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
uint8_t v_res_1036_; lean_object* v_r_1037_; 
v_res_1036_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27___redArg(v_x_1034_, v_x_1035_);
lean_dec_ref(v_x_1035_);
v_r_1037_ = lean_box(v_res_1036_);
return v_r_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(lean_object* v_cls_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_options_1044_; uint8_t v_hasTrace_1045_; 
v_options_1044_ = lean_ctor_get(v___y_1042_, 2);
v_hasTrace_1045_ = lean_ctor_get_uint8(v_options_1044_, sizeof(void*)*1);
if (v_hasTrace_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v_cls_1041_);
v___x_1046_ = lean_box(v_hasTrace_1045_);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
else
{
lean_object* v_inheritedTraceOptions_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_inheritedTraceOptions_1048_ = lean_ctor_get(v___y_1042_, 13);
v___x_1049_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1));
v___x_1050_ = l_Lean_Name_append(v___x_1049_, v_cls_1041_);
v___x_1051_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1048_, v_options_1044_, v___x_1050_);
lean_dec(v___x_1050_);
v___x_1052_ = lean_box(v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___boxed(lean_object* v_cls_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_1054_, v___y_1055_);
lean_dec_ref(v___y_1055_);
return v_res_1057_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__2(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1060_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__1));
v___x_1061_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__0));
v___x_1062_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1061_, v___x_1060_);
return v___x_1062_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__6(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__5));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__8(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__7));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__9(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__1));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__11(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__10));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__13(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__12));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18(lean_object* v_mod_1084_, uint8_t v_isMeta_1085_, lean_object* v_hint_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; lean_object* v_env_1095_; uint8_t v_isExporting_1096_; lean_object* v___x_1097_; lean_object* v_env_1098_; lean_object* v___x_1099_; lean_object* v_entry_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1094_ = lean_st_ref_get(v___y_1092_);
v_env_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc_ref(v_env_1095_);
lean_dec(v___x_1094_);
v_isExporting_1096_ = lean_ctor_get_uint8(v_env_1095_, sizeof(void*)*8);
lean_dec_ref(v_env_1095_);
v___x_1097_ = lean_st_ref_get(v___y_1092_);
v_env_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_env_1098_);
lean_dec(v___x_1097_);
v___x_1099_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__2);
lean_inc(v_mod_1084_);
v_entry_1100_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1100_, 0, v_mod_1084_);
lean_ctor_set_uint8(v_entry_1100_, sizeof(void*)*1, v_isExporting_1096_);
lean_ctor_set_uint8(v_entry_1100_, sizeof(void*)*1 + 1, v_isMeta_1085_);
v___x_1101_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1102_ = lean_box(1);
v___x_1103_ = lean_box(0);
v___x_1146_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1099_, v___x_1101_, v_env_1098_, v___x_1102_, v___x_1103_);
v___x_1147_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27___redArg(v___x_1146_, v_entry_1100_);
if (v___x_1147_ == 0)
{
lean_object* v_cls_1148_; lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1157_; lean_object* v___y_1158_; uint8_t v___x_1170_; 
v_cls_1148_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__4));
v___x_1149_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_1148_, v___y_1091_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref(v___x_1149_);
v___x_1170_ = lean_unbox(v_a_1150_);
lean_dec(v_a_1150_);
if (v___x_1170_ == 0)
{
lean_dec(v_hint_1086_);
lean_dec(v_mod_1084_);
v___y_1105_ = v___y_1090_;
v___y_1106_ = v___y_1092_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1171_; lean_object* v___y_1173_; 
v___x_1171_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__11);
if (v_isExporting_1096_ == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__16));
v___y_1173_ = v___x_1180_;
goto v___jp_1172_;
}
else
{
lean_object* v___x_1181_; 
v___x_1181_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__17));
v___y_1173_ = v___x_1181_;
goto v___jp_1172_;
}
v___jp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1174_ = l_Lean_stringToMessageData(v___y_1173_);
v___x_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1171_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__13);
v___x_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1175_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
if (v_isMeta_1085_ == 0)
{
lean_object* v___x_1178_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__14));
v___y_1157_ = v___x_1177_;
v___y_1158_ = v___x_1178_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__15));
v___y_1157_ = v___x_1177_;
v___y_1158_ = v___x_1179_;
goto v___jp_1156_;
}
}
}
v___jp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___y_1152_);
lean_ctor_set(v___x_1154_, 1, v___y_1153_);
v___x_1155_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_cls_1148_, v___x_1154_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_dec_ref(v___x_1155_);
v___y_1105_ = v___y_1090_;
v___y_1106_ = v___y_1092_;
goto v___jp_1104_;
}
else
{
lean_dec_ref(v_entry_1100_);
return v___x_1155_;
}
}
v___jp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1159_ = l_Lean_stringToMessageData(v___y_1158_);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___y_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__6);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = l_Lean_MessageData_ofName(v_mod_1084_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = l_Lean_Name_isAnonymous(v_hint_1086_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__8);
v___x_1167_ = l_Lean_MessageData_ofName(v_hint_1086_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___y_1152_ = v___x_1164_;
v___y_1153_ = v___x_1168_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1169_; 
lean_dec(v_hint_1086_);
v___x_1169_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___closed__9);
v___y_1152_ = v___x_1164_;
v___y_1153_ = v___x_1169_;
goto v___jp_1151_;
}
}
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec_ref(v_entry_1100_);
lean_dec(v_hint_1086_);
lean_dec(v_mod_1084_);
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
v___jp_1104_:
{
lean_object* v___x_1107_; lean_object* v_toEnvExtension_1108_; lean_object* v_env_1109_; lean_object* v_nextMacroScope_1110_; lean_object* v_ngen_1111_; lean_object* v_auxDeclNGen_1112_; lean_object* v_traceState_1113_; lean_object* v_messages_1114_; lean_object* v_infoState_1115_; lean_object* v_snapshotTasks_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1144_; 
v___x_1107_ = lean_st_ref_take(v___y_1106_);
v_toEnvExtension_1108_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_ref(v_toEnvExtension_1108_);
v_env_1109_ = lean_ctor_get(v___x_1107_, 0);
v_nextMacroScope_1110_ = lean_ctor_get(v___x_1107_, 1);
v_ngen_1111_ = lean_ctor_get(v___x_1107_, 2);
v_auxDeclNGen_1112_ = lean_ctor_get(v___x_1107_, 3);
v_traceState_1113_ = lean_ctor_get(v___x_1107_, 4);
v_messages_1114_ = lean_ctor_get(v___x_1107_, 6);
v_infoState_1115_ = lean_ctor_get(v___x_1107_, 7);
v_snapshotTasks_1116_ = lean_ctor_get(v___x_1107_, 8);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1107_, 5);
lean_dec(v_unused_1145_);
v___x_1118_ = v___x_1107_;
v_isShared_1119_ = v_isSharedCheck_1144_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_snapshotTasks_1116_);
lean_inc(v_infoState_1115_);
lean_inc(v_messages_1114_);
lean_inc(v_traceState_1113_);
lean_inc(v_auxDeclNGen_1112_);
lean_inc(v_ngen_1111_);
lean_inc(v_nextMacroScope_1110_);
lean_inc(v_env_1109_);
lean_dec(v___x_1107_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1144_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_asyncMode_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v_asyncMode_1120_ = lean_ctor_get(v_toEnvExtension_1108_, 2);
lean_inc(v_asyncMode_1120_);
lean_dec_ref(v_toEnvExtension_1108_);
v___x_1121_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1101_, v_env_1109_, v_entry_1100_, v_asyncMode_1120_, v___x_1103_);
lean_dec(v_asyncMode_1120_);
v___x_1122_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 5, v___x_1122_);
lean_ctor_set(v___x_1118_, 0, v___x_1121_);
v___x_1124_ = v___x_1118_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_nextMacroScope_1110_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_ngen_1111_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_auxDeclNGen_1112_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_traceState_1113_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1143_, 6, v_messages_1114_);
lean_ctor_set(v_reuseFailAlloc_1143_, 7, v_infoState_1115_);
lean_ctor_set(v_reuseFailAlloc_1143_, 8, v_snapshotTasks_1116_);
v___x_1124_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_mctx_1127_; lean_object* v_zetaDeltaFVarIds_1128_; lean_object* v_postponed_1129_; lean_object* v_diag_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1141_; 
v___x_1125_ = lean_st_ref_set(v___y_1106_, v___x_1124_);
v___x_1126_ = lean_st_ref_take(v___y_1105_);
v_mctx_1127_ = lean_ctor_get(v___x_1126_, 0);
v_zetaDeltaFVarIds_1128_ = lean_ctor_get(v___x_1126_, 2);
v_postponed_1129_ = lean_ctor_get(v___x_1126_, 3);
v_diag_1130_ = lean_ctor_get(v___x_1126_, 4);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v___x_1126_, 1);
lean_dec(v_unused_1142_);
v___x_1132_ = v___x_1126_;
v_isShared_1133_ = v_isSharedCheck_1141_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_diag_1130_);
lean_inc(v_postponed_1129_);
lean_inc(v_zetaDeltaFVarIds_1128_);
lean_inc(v_mctx_1127_);
lean_dec(v___x_1126_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1141_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_mctx_1127_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_zetaDeltaFVarIds_1128_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_postponed_1129_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_diag_1130_);
v___x_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_st_ref_set(v___y_1105_, v___x_1136_);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18___boxed(lean_object* v_mod_1184_, lean_object* v_isMeta_1185_, lean_object* v_hint_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
uint8_t v_isMeta_boxed_1194_; lean_object* v_res_1195_; 
v_isMeta_boxed_1194_ = lean_unbox(v_isMeta_1185_);
v_res_1195_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18(v_mod_1184_, v_isMeta_boxed_1194_, v_hint_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__19(lean_object* v___x_1196_, lean_object* v_declName_1197_, lean_object* v_as_1198_, size_t v_sz_1199_, size_t v_i_1200_, lean_object* v_b_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_usize_dec_lt(v_i_1200_, v_sz_1199_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
lean_dec(v_declName_1197_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_b_1201_);
return v___x_1210_;
}
else
{
lean_object* v___x_1211_; lean_object* v_modules_1212_; lean_object* v___x_1213_; lean_object* v_a_1214_; lean_object* v___x_1215_; lean_object* v_toImport_1216_; lean_object* v_module_1217_; uint8_t v___x_1218_; lean_object* v___x_1219_; 
v___x_1211_ = l_Lean_Environment_header(v___x_1196_);
v_modules_1212_ = lean_ctor_get(v___x_1211_, 3);
lean_inc_ref(v_modules_1212_);
lean_dec_ref(v___x_1211_);
v___x_1213_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1214_ = lean_array_uget_borrowed(v_as_1198_, v_i_1200_);
v___x_1215_ = lean_array_get(v___x_1213_, v_modules_1212_, v_a_1214_);
lean_dec_ref(v_modules_1212_);
v_toImport_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_ref(v_toImport_1216_);
lean_dec(v___x_1215_);
v_module_1217_ = lean_ctor_get(v_toImport_1216_, 0);
lean_inc(v_module_1217_);
lean_dec_ref(v_toImport_1216_);
v___x_1218_ = 0;
lean_inc(v_declName_1197_);
v___x_1219_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18(v_module_1217_, v___x_1218_, v_declName_1197_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; size_t v___x_1221_; size_t v___x_1222_; 
lean_dec_ref(v___x_1219_);
v___x_1220_ = lean_box(0);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_add(v_i_1200_, v___x_1221_);
v_i_1200_ = v___x_1222_;
v_b_1201_ = v___x_1220_;
goto _start;
}
else
{
lean_dec(v_declName_1197_);
return v___x_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__19___boxed(lean_object* v___x_1224_, lean_object* v_declName_1225_, lean_object* v_as_1226_, lean_object* v_sz_1227_, lean_object* v_i_1228_, lean_object* v_b_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1227_);
lean_dec(v_sz_1227_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1228_);
lean_dec(v_i_1228_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__19(v___x_1224_, v_declName_1225_, v_as_1226_, v_sz_boxed_1237_, v_i_boxed_1238_, v_b_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v_as_1226_);
lean_dec_ref(v___x_1224_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30___redArg(lean_object* v_a_1240_, lean_object* v_x_1241_){
_start:
{
if (lean_obj_tag(v_x_1241_) == 0)
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_box(0);
return v___x_1242_;
}
else
{
lean_object* v_key_1243_; lean_object* v_value_1244_; lean_object* v_tail_1245_; uint8_t v___x_1246_; 
v_key_1243_ = lean_ctor_get(v_x_1241_, 0);
v_value_1244_ = lean_ctor_get(v_x_1241_, 1);
v_tail_1245_ = lean_ctor_get(v_x_1241_, 2);
v___x_1246_ = lean_name_eq(v_key_1243_, v_a_1240_);
if (v___x_1246_ == 0)
{
v_x_1241_ = v_tail_1245_;
goto _start;
}
else
{
lean_object* v___x_1248_; 
lean_inc(v_value_1244_);
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v_value_1244_);
return v___x_1248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30___redArg___boxed(lean_object* v_a_1249_, lean_object* v_x_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30___redArg(v_a_1249_, v_x_1250_);
lean_dec(v_x_1250_);
lean_dec(v_a_1249_);
return v_res_1251_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg___closed__0(void){
_start:
{
lean_object* v___x_1252_; uint64_t v___x_1253_; 
v___x_1252_ = lean_unsigned_to_nat(1723u);
v___x_1253_ = lean_uint64_of_nat(v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg(lean_object* v_m_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_buckets_1256_; lean_object* v___x_1257_; uint64_t v___y_1259_; 
v_buckets_1256_ = lean_ctor_get(v_m_1254_, 1);
v___x_1257_ = lean_array_get_size(v_buckets_1256_);
if (lean_obj_tag(v_a_1255_) == 0)
{
uint64_t v___x_1273_; 
v___x_1273_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg___closed__0);
v___y_1259_ = v___x_1273_;
goto v___jp_1258_;
}
else
{
uint64_t v_hash_1274_; 
v_hash_1274_ = lean_ctor_get_uint64(v_a_1255_, sizeof(void*)*2);
v___y_1259_ = v_hash_1274_;
goto v___jp_1258_;
}
v___jp_1258_:
{
uint64_t v___x_1260_; uint64_t v___x_1261_; uint64_t v_fold_1262_; uint64_t v___x_1263_; uint64_t v___x_1264_; uint64_t v___x_1265_; size_t v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1260_ = 32ULL;
v___x_1261_ = lean_uint64_shift_right(v___y_1259_, v___x_1260_);
v_fold_1262_ = lean_uint64_xor(v___y_1259_, v___x_1261_);
v___x_1263_ = 16ULL;
v___x_1264_ = lean_uint64_shift_right(v_fold_1262_, v___x_1263_);
v___x_1265_ = lean_uint64_xor(v_fold_1262_, v___x_1264_);
v___x_1266_ = lean_uint64_to_usize(v___x_1265_);
v___x_1267_ = lean_usize_of_nat(v___x_1257_);
v___x_1268_ = ((size_t)1ULL);
v___x_1269_ = lean_usize_sub(v___x_1267_, v___x_1268_);
v___x_1270_ = lean_usize_land(v___x_1266_, v___x_1269_);
v___x_1271_ = lean_array_uget_borrowed(v_buckets_1256_, v___x_1270_);
v___x_1272_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30___redArg(v_a_1255_, v___x_1271_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg___boxed(lean_object* v_m_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg(v_m_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_m_1275_);
return v_res_1277_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__2(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__1));
v___x_1281_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__0));
v___x_1282_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1281_, v___x_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(lean_object* v_declName_1285_, uint8_t v_isMeta_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; lean_object* v_env_1298_; lean_object* v___y_1300_; lean_object* v___x_1313_; 
v___x_1294_ = lean_st_ref_get(v___y_1292_);
v_env_1298_ = lean_ctor_get(v___x_1294_, 0);
lean_inc_ref(v_env_1298_);
lean_dec(v___x_1294_);
v___x_1313_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1298_, v_declName_1285_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_dec_ref(v_env_1298_);
lean_dec(v_declName_1285_);
goto v___jp_1295_;
}
else
{
lean_object* v_val_1314_; lean_object* v___x_1315_; lean_object* v_modules_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_val_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_val_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = l_Lean_Environment_header(v_env_1298_);
v_modules_1316_ = lean_ctor_get(v___x_1315_, 3);
lean_inc_ref(v_modules_1316_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = lean_array_get_size(v_modules_1316_);
v___x_1318_ = lean_nat_dec_lt(v_val_1314_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec_ref(v_modules_1316_);
lean_dec(v_val_1314_);
lean_dec_ref(v_env_1298_);
lean_dec(v_declName_1285_);
goto v___jp_1295_;
}
else
{
lean_object* v___x_1319_; lean_object* v_env_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___y_1324_; 
v___x_1319_ = lean_st_ref_get(v___y_1292_);
v_env_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc_ref(v_env_1320_);
lean_dec(v___x_1319_);
v___x_1321_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__2);
v___x_1322_ = lean_array_fget(v_modules_1316_, v_val_1314_);
lean_dec(v_val_1314_);
lean_dec_ref(v_modules_1316_);
if (v_isMeta_1286_ == 0)
{
lean_dec_ref(v_env_1320_);
v___y_1324_ = v_isMeta_1286_;
goto v___jp_1323_;
}
else
{
uint8_t v___x_1335_; 
lean_inc(v_declName_1285_);
v___x_1335_ = l_Lean_isMarkedMeta(v_env_1320_, v_declName_1285_);
if (v___x_1335_ == 0)
{
v___y_1324_ = v_isMeta_1286_;
goto v___jp_1323_;
}
else
{
uint8_t v___x_1336_; 
v___x_1336_ = 0;
v___y_1324_ = v___x_1336_;
goto v___jp_1323_;
}
}
v___jp_1323_:
{
lean_object* v_toImport_1325_; lean_object* v_module_1326_; lean_object* v___x_1327_; 
v_toImport_1325_ = lean_ctor_get(v___x_1322_, 0);
lean_inc_ref(v_toImport_1325_);
lean_dec(v___x_1322_);
v_module_1326_ = lean_ctor_get(v_toImport_1325_, 0);
lean_inc(v_module_1326_);
lean_dec_ref(v_toImport_1325_);
lean_inc(v_declName_1285_);
v___x_1327_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18(v_module_1326_, v___y_1324_, v_declName_1285_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v___x_1327_);
v___x_1328_ = l_Lean_indirectModUseExt;
v___x_1329_ = lean_box(1);
v___x_1330_ = lean_box(0);
lean_inc_ref(v_env_1298_);
v___x_1331_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1321_, v___x_1328_, v_env_1298_, v___x_1329_, v___x_1330_);
v___x_1332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg(v___x_1331_, v_declName_1285_);
lean_dec(v___x_1331_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v___x_1333_; 
v___x_1333_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___closed__3));
v___y_1300_ = v___x_1333_;
goto v___jp_1299_;
}
else
{
lean_object* v_val_1334_; 
v_val_1334_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_val_1334_);
lean_dec_ref(v___x_1332_);
v___y_1300_ = v_val_1334_;
goto v___jp_1299_;
}
}
else
{
lean_dec_ref(v_env_1298_);
lean_dec(v_declName_1285_);
return v___x_1327_;
}
}
}
}
v___jp_1295_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
return v___x_1297_;
}
v___jp_1299_:
{
lean_object* v___x_1301_; size_t v_sz_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v___x_1301_ = lean_box(0);
v_sz_1302_ = lean_array_size(v___y_1300_);
v___x_1303_ = ((size_t)0ULL);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__19(v_env_1298_, v_declName_1285_, v___y_1300_, v_sz_1302_, v___x_1303_, v___x_1301_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec_ref(v___y_1300_);
lean_dec_ref(v_env_1298_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v___x_1304_, 0);
lean_dec(v_unused_1312_);
v___x_1306_ = v___x_1304_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_dec(v___x_1304_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1301_);
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1301_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___boxed(lean_object* v_declName_1337_, lean_object* v_isMeta_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_isMeta_boxed_1346_; lean_object* v_res_1347_; 
v_isMeta_boxed_1346_ = lean_unbox(v_isMeta_1338_);
v_res_1347_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(v_declName_1337_, v_isMeta_boxed_1346_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___redArg(lean_object* v_x_1348_, lean_object* v___y_1349_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v_x_1348_, 0);
lean_inc(v_a_1350_);
v___x_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_a_1350_);
lean_ctor_set(v___x_1351_, 1, v___y_1349_);
return v___x_1351_;
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1353_; 
v_a_1352_ = lean_ctor_get(v_x_1348_, 0);
lean_inc(v_a_1352_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_a_1352_);
lean_ctor_set(v___x_1353_, 1, v___y_1349_);
return v___x_1353_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___redArg___boxed(lean_object* v_x_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___redArg(v_x_1354_, v___y_1355_);
lean_dec_ref(v_x_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(lean_object* v_env_1357_, lean_object* v_stx_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1357_, v_stx_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
if (lean_obj_tag(v_a_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1371_; 
v_a_1363_ = lean_ctor_get(v___x_1361_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v___x_1361_, 0);
lean_dec(v_unused_1372_);
v___x_1365_ = v___x_1361_;
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = lean_box(0);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1367_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_a_1363_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
lean_object* v_val_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1401_; 
v_val_1373_ = lean_ctor_get(v_a_1362_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_a_1362_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1375_ = v_a_1362_;
v_isShared_1376_ = v_isSharedCheck_1401_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_val_1373_);
lean_dec(v_a_1362_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1401_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_snd_1377_; 
v_snd_1377_ = lean_ctor_get(v_val_1373_, 1);
lean_inc(v_snd_1377_);
lean_dec(v_val_1373_);
if (lean_obj_tag(v_snd_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1387_; 
lean_del_object(v___x_1375_);
v_a_1378_ = lean_ctor_get(v___x_1361_, 1);
lean_inc(v_a_1378_);
lean_dec_ref(v___x_1361_);
v_a_1379_ = lean_ctor_get(v_snd_1377_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_snd_1377_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1381_ = v_snd_1377_;
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v_snd_1377_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___redArg(v___x_1384_, v_a_1378_);
lean_dec_ref(v___x_1384_);
return v___x_1385_;
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1400_; 
v_a_1388_ = lean_ctor_get(v___x_1361_, 1);
lean_inc(v_a_1388_);
lean_dec_ref(v___x_1361_);
v_a_1389_ = lean_ctor_get(v_snd_1377_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_snd_1377_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1391_ = v_snd_1377_;
v_isShared_1392_ = v_isSharedCheck_1400_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v_snd_1377_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1400_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_a_1389_);
v___x_1394_ = v___x_1375_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1396_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1394_);
v___x_1396_ = v___x_1391_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___redArg(v___x_1396_, v_a_1388_);
lean_dec_ref(v___x_1396_);
return v___x_1397_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1402_ = lean_ctor_get(v___x_1361_, 0);
v_a_1403_ = lean_ctor_get(v___x_1361_, 1);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1361_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_inc(v_a_1402_);
lean_dec(v___x_1361_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1402_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed(lean_object* v_env_1411_, lean_object* v_stx_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(v_env_1411_, v_stx_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(lean_object* v_env_1416_, lean_object* v_options_1417_, lean_object* v_currNamespace_1418_, lean_object* v_openDecls_1419_, lean_object* v_n_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = l_Lean_ResolveName_resolveGlobalName(v_env_1416_, v_options_1417_, v_currNamespace_1418_, v_openDecls_1419_, v_n_1420_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v___y_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed(lean_object* v_env_1425_, lean_object* v_options_1426_, lean_object* v_currNamespace_1427_, lean_object* v_openDecls_1428_, lean_object* v_n_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(v_env_1425_, v_options_1426_, v_currNamespace_1427_, v_openDecls_1428_, v_n_1429_, v___y_1430_, v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec_ref(v_options_1426_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(lean_object* v_currNamespace_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_currNamespace_1433_);
lean_ctor_set(v___x_1436_, 1, v___y_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed(lean_object* v_currNamespace_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(v_currNamespace_1437_, v___y_1438_, v___y_1439_);
lean_dec_ref(v___y_1438_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(lean_object* v_env_1441_, lean_object* v_declName_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v___x_1445_; lean_object* v_env_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; uint8_t v___x_1449_; 
v___x_1445_ = 0;
v_env_1446_ = l_Lean_Environment_setExporting(v_env_1441_, v___x_1445_);
lean_inc(v_declName_1442_);
v___x_1447_ = l_Lean_mkPrivateName(v_env_1446_, v_declName_1442_);
v___x_1448_ = 1;
lean_inc_ref(v_env_1446_);
v___x_1449_ = l_Lean_Environment_contains(v_env_1446_, v___x_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1450_ = l_Lean_privateToUserName(v_declName_1442_);
v___x_1451_ = l_Lean_Environment_contains(v_env_1446_, v___x_1450_, v___x_1448_);
v___x_1452_ = lean_box(v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v___y_1444_);
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v_env_1446_);
lean_dec(v_declName_1442_);
v___x_1454_ = lean_box(v___x_1449_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___y_1444_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed(lean_object* v_env_1456_, lean_object* v_declName_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(v_env_1456_, v_declName_1457_, v___y_1458_, v___y_1459_);
lean_dec_ref(v___y_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___redArg(lean_object* v_as_x27_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
if (lean_obj_tag(v_as_x27_1461_) == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1462_);
return v___x_1470_;
}
else
{
lean_object* v_head_1471_; lean_object* v_tail_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; 
v_head_1471_ = lean_ctor_get(v_as_x27_1461_, 0);
lean_inc(v_head_1471_);
v_tail_1472_ = lean_ctor_get(v_as_x27_1461_, 1);
lean_inc(v_tail_1472_);
lean_dec_ref(v_as_x27_1461_);
v___x_1473_ = 1;
v___x_1474_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(v_head_1471_, v___x_1473_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v___x_1475_; 
lean_dec_ref(v___x_1474_);
v___x_1475_ = lean_box(0);
v_as_x27_1461_ = v_tail_1472_;
v_b_1462_ = v___x_1475_;
goto _start;
}
else
{
lean_dec(v_tail_1472_);
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___redArg___boxed(lean_object* v_as_x27_1477_, lean_object* v_b_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___redArg(v_as_x27_1477_, v_b_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(lean_object* v_env_1487_, lean_object* v_currNamespace_1488_, lean_object* v_openDecls_1489_, lean_object* v_n_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = l_Lean_ResolveName_resolveNamespace(v_env_1487_, v_currNamespace_1488_, v_openDecls_1489_, v_n_1490_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___y_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed(lean_object* v_env_1495_, lean_object* v_currNamespace_1496_, lean_object* v_openDecls_1497_, lean_object* v_n_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(v_env_1495_, v_currNamespace_1496_, v_openDecls_1497_, v_n_1498_, v___y_1499_, v___y_1500_);
lean_dec_ref(v___y_1499_);
return v_res_1501_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = l_Lean_maxRecDepthErrorMessage;
v___x_1508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__4(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__3);
v___x_1510_ = l_Lean_MessageData_ofFormat(v___x_1509_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__4);
v___x_1512_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__2));
v___x_1513_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
lean_ctor_set(v___x_1513_, 1, v___x_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg(lean_object* v_ref_1514_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___closed__5);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_ref_1514_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg___boxed(lean_object* v_ref_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg(v_ref_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(lean_object* v_as_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
if (lean_obj_tag(v_as_1522_) == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
else
{
lean_object* v_head_1532_; lean_object* v_tail_1533_; lean_object* v_fst_1534_; lean_object* v_snd_1535_; lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1549_; 
v_head_1532_ = lean_ctor_get(v_as_1522_, 0);
lean_inc(v_head_1532_);
v_tail_1533_ = lean_ctor_get(v_as_1522_, 1);
lean_inc(v_tail_1533_);
lean_dec_ref(v_as_1522_);
v_fst_1534_ = lean_ctor_get(v_head_1532_, 0);
lean_inc(v_fst_1534_);
v_snd_1535_ = lean_ctor_get(v_head_1532_, 1);
lean_inc(v_snd_1535_);
lean_dec(v_head_1532_);
lean_inc(v_fst_1534_);
v___x_1536_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_fst_1534_, v___y_1527_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1549_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1549_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
uint8_t v___x_1541_; 
v___x_1541_ = lean_unbox(v_a_1537_);
lean_dec(v_a_1537_);
if (v___x_1541_ == 0)
{
lean_del_object(v___x_1539_);
lean_dec(v_snd_1535_);
lean_dec(v_fst_1534_);
v_as_1522_ = v_tail_1533_;
goto _start;
}
else
{
lean_object* v___x_1544_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 3);
lean_ctor_set(v___x_1539_, 0, v_snd_1535_);
v___x_1544_ = v___x_1539_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_snd_1535_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = l_Lean_MessageData_ofFormat(v___x_1544_);
v___x_1546_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_fst_1534_, v___x_1545_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_dec_ref(v___x_1546_);
v_as_1522_ = v_tail_1533_;
goto _start;
}
else
{
lean_dec(v_tail_1533_);
return v___x_1546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___boxed(lean_object* v_as_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(v_as_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(lean_object* v_x_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; lean_object* v_env_1569_; lean_object* v_options_1570_; lean_object* v_currRecDepth_1571_; lean_object* v_maxRecDepth_1572_; lean_object* v_ref_1573_; lean_object* v_currNamespace_1574_; lean_object* v_openDecls_1575_; lean_object* v_quotContext_1576_; lean_object* v_currMacroScope_1577_; lean_object* v___x_1578_; lean_object* v_nextMacroScope_1579_; lean_object* v___f_1580_; lean_object* v___f_1581_; lean_object* v___f_1582_; lean_object* v___f_1583_; lean_object* v___f_1584_; lean_object* v_methods_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1568_ = lean_st_ref_get(v___y_1566_);
v_env_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_ref(v_env_1569_);
lean_dec(v___x_1568_);
v_options_1570_ = lean_ctor_get(v___y_1565_, 2);
v_currRecDepth_1571_ = lean_ctor_get(v___y_1565_, 3);
v_maxRecDepth_1572_ = lean_ctor_get(v___y_1565_, 4);
v_ref_1573_ = lean_ctor_get(v___y_1565_, 5);
v_currNamespace_1574_ = lean_ctor_get(v___y_1565_, 6);
v_openDecls_1575_ = lean_ctor_get(v___y_1565_, 7);
v_quotContext_1576_ = lean_ctor_get(v___y_1565_, 10);
v_currMacroScope_1577_ = lean_ctor_get(v___y_1565_, 11);
v___x_1578_ = lean_st_ref_get(v___y_1566_);
v_nextMacroScope_1579_ = lean_ctor_get(v___x_1578_, 1);
lean_inc(v_nextMacroScope_1579_);
lean_dec(v___x_1578_);
lean_inc_ref(v_env_1569_);
v___f_1580_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1580_, 0, v_env_1569_);
lean_inc_ref(v_env_1569_);
v___f_1581_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1581_, 0, v_env_1569_);
lean_inc(v_openDecls_1575_);
lean_inc(v_currNamespace_1574_);
lean_inc_ref(v_env_1569_);
v___f_1582_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1582_, 0, v_env_1569_);
lean_closure_set(v___f_1582_, 1, v_currNamespace_1574_);
lean_closure_set(v___f_1582_, 2, v_openDecls_1575_);
lean_inc(v_currNamespace_1574_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1583_, 0, v_currNamespace_1574_);
lean_inc(v_openDecls_1575_);
lean_inc(v_currNamespace_1574_);
lean_inc_ref(v_options_1570_);
v___f_1584_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1584_, 0, v_env_1569_);
lean_closure_set(v___f_1584_, 1, v_options_1570_);
lean_closure_set(v___f_1584_, 2, v_currNamespace_1574_);
lean_closure_set(v___f_1584_, 3, v_openDecls_1575_);
v_methods_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1585_, 0, v___f_1580_);
lean_ctor_set(v_methods_1585_, 1, v___f_1583_);
lean_ctor_set(v_methods_1585_, 2, v___f_1581_);
lean_ctor_set(v_methods_1585_, 3, v___f_1582_);
lean_ctor_set(v_methods_1585_, 4, v___f_1584_);
lean_inc(v_ref_1573_);
lean_inc(v_maxRecDepth_1572_);
lean_inc(v_currRecDepth_1571_);
lean_inc(v_currMacroScope_1577_);
lean_inc(v_quotContext_1576_);
v___x_1586_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1586_, 0, v_methods_1585_);
lean_ctor_set(v___x_1586_, 1, v_quotContext_1576_);
lean_ctor_set(v___x_1586_, 2, v_currMacroScope_1577_);
lean_ctor_set(v___x_1586_, 3, v_currRecDepth_1571_);
lean_ctor_set(v___x_1586_, 4, v_maxRecDepth_1572_);
lean_ctor_set(v___x_1586_, 5, v_ref_1573_);
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1588_, 0, v_nextMacroScope_1579_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
lean_ctor_set(v___x_1588_, 2, v___x_1587_);
v___x_1589_ = lean_apply_2(v_x_1560_, v___x_1586_, v___x_1588_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v_a_1591_; lean_object* v_macroScope_1592_; lean_object* v_traceMsgs_1593_; lean_object* v_expandedMacroDecls_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 1);
lean_inc(v_a_1590_);
v_a_1591_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1589_);
v_macroScope_1592_ = lean_ctor_get(v_a_1590_, 0);
lean_inc(v_macroScope_1592_);
v_traceMsgs_1593_ = lean_ctor_get(v_a_1590_, 1);
lean_inc(v_traceMsgs_1593_);
v_expandedMacroDecls_1594_ = lean_ctor_get(v_a_1590_, 2);
lean_inc(v_expandedMacroDecls_1594_);
lean_dec(v_a_1590_);
v___x_1595_ = lean_box(0);
v___x_1596_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___redArg(v_expandedMacroDecls_1594_, v___x_1595_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1597_; lean_object* v_env_1598_; lean_object* v_ngen_1599_; lean_object* v_auxDeclNGen_1600_; lean_object* v_traceState_1601_; lean_object* v_cache_1602_; lean_object* v_messages_1603_; lean_object* v_infoState_1604_; lean_object* v_snapshotTasks_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v___x_1596_);
v___x_1597_ = lean_st_ref_take(v___y_1566_);
v_env_1598_ = lean_ctor_get(v___x_1597_, 0);
v_ngen_1599_ = lean_ctor_get(v___x_1597_, 2);
v_auxDeclNGen_1600_ = lean_ctor_get(v___x_1597_, 3);
v_traceState_1601_ = lean_ctor_get(v___x_1597_, 4);
v_cache_1602_ = lean_ctor_get(v___x_1597_, 5);
v_messages_1603_ = lean_ctor_get(v___x_1597_, 6);
v_infoState_1604_ = lean_ctor_get(v___x_1597_, 7);
v_snapshotTasks_1605_ = lean_ctor_get(v___x_1597_, 8);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v___x_1597_, 1);
lean_dec(v_unused_1632_);
v___x_1607_ = v___x_1597_;
v_isShared_1608_ = v_isSharedCheck_1631_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_snapshotTasks_1605_);
lean_inc(v_infoState_1604_);
lean_inc(v_messages_1603_);
lean_inc(v_cache_1602_);
lean_inc(v_traceState_1601_);
lean_inc(v_auxDeclNGen_1600_);
lean_inc(v_ngen_1599_);
lean_inc(v_env_1598_);
lean_dec(v___x_1597_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1631_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 1, v_macroScope_1592_);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_env_1598_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_macroScope_1592_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_ngen_1599_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_auxDeclNGen_1600_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_traceState_1601_);
lean_ctor_set(v_reuseFailAlloc_1630_, 5, v_cache_1602_);
lean_ctor_set(v_reuseFailAlloc_1630_, 6, v_messages_1603_);
lean_ctor_set(v_reuseFailAlloc_1630_, 7, v_infoState_1604_);
lean_ctor_set(v_reuseFailAlloc_1630_, 8, v_snapshotTasks_1605_);
v___x_1610_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = lean_st_ref_set(v___y_1566_, v___x_1610_);
v___x_1612_ = l_List_reverse___redArg(v_traceMsgs_1593_);
v___x_1613_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(v___x_1612_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v___y_1561_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; 
v_unused_1621_ = lean_ctor_get(v___x_1613_, 0);
lean_dec(v_unused_1621_);
v___x_1615_ = v___x_1613_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_dec(v___x_1613_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v_a_1591_);
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1591_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1591_);
v_a_1622_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1613_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1613_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v_traceMsgs_1593_);
lean_dec(v_macroScope_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v___y_1561_);
v_a_1633_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1596_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1596_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
lean_object* v_a_1641_; 
v_a_1641_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v___x_1589_);
if (lean_obj_tag(v_a_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_a_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v_a_1642_ = lean_ctor_get(v_a_1641_, 0);
lean_inc(v_a_1642_);
v_a_1643_ = lean_ctor_get(v_a_1641_, 1);
lean_inc_ref(v_a_1643_);
lean_dec_ref(v_a_1641_);
v___x_1644_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0));
v___x_1645_ = lean_string_dec_eq(v_a_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_a_1643_);
v___x_1647_ = l_Lean_MessageData_ofFormat(v___x_1646_);
v___x_1648_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_a_1642_, v___x_1647_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v_a_1642_);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; 
lean_dec_ref(v_a_1643_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v___y_1561_);
v___x_1649_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg(v_a_1642_);
return v___x_1649_;
}
}
else
{
lean_object* v___x_1650_; 
lean_dec_ref(v___y_1565_);
lean_dec_ref(v___y_1561_);
v___x_1650_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___boxed(lean_object* v_x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v_x_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
return v_res_1659_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__0));
v___x_1662_ = l_Lean_stringToMessageData(v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__2));
v___x_1665_ = l_Lean_stringToMessageData(v___x_1664_);
return v___x_1665_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__7));
v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1(lean_object* v___x_1676_, lean_object* v_attrInstance_1677_, lean_object* v___f_1678_, lean_object* v___x_1679_, lean_object* v___x_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
lean_inc_ref(v___y_1685_);
lean_inc_ref(v___y_1681_);
v___x_1688_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_1676_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; lean_object* v_attr_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref(v___x_1688_);
v___x_1690_ = lean_unsigned_to_nat(1u);
v_attr_1691_ = l_Lean_Syntax_getArg(v_attrInstance_1677_, v___x_1690_);
v___x_1692_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_1692_, 0, v_attr_1691_);
lean_closure_set(v___x_1692_, 1, v___f_1678_);
lean_inc_ref(v___y_1685_);
lean_inc_ref(v___y_1681_);
v___x_1693_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_1692_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1761_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1761_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1761_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___y_1699_; lean_object* v_attrName_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
lean_inc(v_a_1694_);
v___x_1742_ = l_Lean_Syntax_getKind(v_a_1694_);
v___x_1743_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__6));
v___x_1744_ = lean_name_eq(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
if (lean_obj_tag(v___x_1742_) == 1)
{
lean_object* v_str_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_str_1745_ = lean_ctor_get(v___x_1742_, 1);
lean_inc_ref(v_str_1745_);
lean_dec_ref(v___x_1742_);
v___x_1746_ = lean_box(0);
v___x_1747_ = l_Lean_Name_str___override(v___x_1746_, v_str_1745_);
v_attrName_1706_ = v___x_1747_;
v___y_1707_ = v___y_1681_;
v___y_1708_ = v___y_1682_;
v___y_1709_ = v___y_1683_;
v___y_1710_ = v___y_1684_;
v___y_1711_ = v___y_1685_;
v___y_1712_ = v___y_1686_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v___x_1742_);
lean_del_object(v___x_1696_);
lean_dec(v_a_1689_);
lean_dec(v___x_1679_);
v___x_1748_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__8, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__8_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__8);
v___x_1749_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_a_1694_, v___x_1748_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v_a_1694_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1749_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1749_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v___x_1742_);
v___x_1758_ = l_Lean_Syntax_getArg(v_a_1694_, v___x_1680_);
v___x_1759_ = l_Lean_Syntax_getId(v___x_1758_);
lean_dec(v___x_1758_);
v___x_1760_ = lean_erase_macro_scopes(v___x_1759_);
v_attrName_1706_ = v___x_1760_;
v___y_1707_ = v___y_1681_;
v___y_1708_ = v___y_1682_;
v___y_1709_ = v___y_1683_;
v___y_1710_ = v___y_1684_;
v___y_1711_ = v___y_1685_;
v___y_1712_ = v___y_1686_;
goto v___jp_1705_;
}
v___jp_1698_:
{
lean_object* v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1703_; 
v___x_1700_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1700_, 0, v___y_1699_);
lean_ctor_set(v___x_1700_, 1, v_a_1694_);
v___x_1701_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*2, v___x_1701_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1700_);
v___x_1703_ = v___x_1696_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1700_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
v___jp_1705_:
{
lean_object* v___x_1713_; lean_object* v_env_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_st_ref_get(v___y_1712_);
v_env_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc_ref(v_env_1714_);
lean_dec(v___x_1713_);
lean_inc(v_attrName_1706_);
v___x_1715_ = l_Lean_getAttributeImpl(v_env_1714_, v_attrName_1706_);
if (lean_obj_tag(v___x_1715_) == 1)
{
lean_object* v___x_1716_; lean_object* v_env_1717_; lean_object* v___x_1718_; 
lean_dec_ref(v___x_1715_);
v___x_1716_ = lean_st_ref_get(v___y_1712_);
v_env_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc_ref(v_env_1717_);
lean_dec(v___x_1716_);
lean_inc(v_attrName_1706_);
v___x_1718_ = l_Lean_getAttributeImpl(v_env_1717_, v_attrName_1706_);
if (lean_obj_tag(v___x_1718_) == 1)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v_toAttributeImplCore_1721_; lean_object* v_env_1722_; lean_object* v_ref_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = lean_st_ref_get(v___y_1712_);
v_toAttributeImplCore_1721_ = lean_ctor_get(v_a_1719_, 0);
lean_inc_ref(v_toAttributeImplCore_1721_);
lean_dec(v_a_1719_);
v_env_1722_ = lean_ctor_get(v___x_1720_, 0);
lean_inc_ref(v_env_1722_);
lean_dec(v___x_1720_);
v_ref_1723_ = lean_ctor_get(v_toAttributeImplCore_1721_, 0);
lean_inc(v_ref_1723_);
lean_dec_ref(v_toAttributeImplCore_1721_);
v___x_1724_ = l_Lean_regularInitAttr;
lean_inc(v_ref_1723_);
v___x_1725_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1679_, v___x_1724_, v_env_1722_, v_ref_1723_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_dec(v_ref_1723_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v___y_1707_);
v___y_1699_ = v_attrName_1706_;
goto v___jp_1698_;
}
else
{
uint8_t v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v___x_1725_);
v___x_1726_ = 1;
v___x_1727_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(v_ref_1723_, v___x_1726_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v___y_1707_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_dec_ref(v___x_1727_);
v___y_1699_ = v_attrName_1706_;
goto v___jp_1698_;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec(v_attrName_1706_);
lean_del_object(v___x_1696_);
lean_dec(v_a_1694_);
lean_dec(v_a_1689_);
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1718_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v___y_1707_);
lean_dec(v___x_1679_);
v___y_1699_ = v_attrName_1706_;
goto v___jp_1698_;
}
}
else
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec_ref(v___x_1715_);
lean_del_object(v___x_1696_);
lean_dec(v_a_1694_);
lean_dec(v_a_1689_);
lean_dec(v___x_1679_);
v___x_1736_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__1, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__1_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__1);
v___x_1737_ = l_Lean_MessageData_ofName(v_attrName_1706_);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__3, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__3_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___closed__3);
v___x_1740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_1740_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec_ref(v___y_1711_);
return v___x_1741_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1689_);
lean_dec_ref(v___y_1685_);
lean_dec_ref(v___y_1681_);
lean_dec(v___x_1679_);
v_a_1762_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1693_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1693_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v___y_1685_);
lean_dec_ref(v___y_1681_);
lean_dec(v___x_1679_);
lean_dec_ref(v___f_1678_);
v_a_1770_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1688_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1688_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___boxed(lean_object* v___x_1778_, lean_object* v_attrInstance_1779_, lean_object* v___f_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1(v___x_1778_, v_attrInstance_1779_, v___f_1780_, v___x_1781_, v___x_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec(v___x_1782_);
lean_dec(v_attrInstance_1779_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg___lam__0(lean_object* v___y_1791_, uint8_t v_isExporting_1792_, lean_object* v___x_1793_, lean_object* v___y_1794_, lean_object* v___x_1795_, lean_object* v_a_x3f_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v_env_1799_; lean_object* v_nextMacroScope_1800_; lean_object* v_ngen_1801_; lean_object* v_auxDeclNGen_1802_; lean_object* v_traceState_1803_; lean_object* v_messages_1804_; lean_object* v_infoState_1805_; lean_object* v_snapshotTasks_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1831_; 
v___x_1798_ = lean_st_ref_take(v___y_1791_);
v_env_1799_ = lean_ctor_get(v___x_1798_, 0);
v_nextMacroScope_1800_ = lean_ctor_get(v___x_1798_, 1);
v_ngen_1801_ = lean_ctor_get(v___x_1798_, 2);
v_auxDeclNGen_1802_ = lean_ctor_get(v___x_1798_, 3);
v_traceState_1803_ = lean_ctor_get(v___x_1798_, 4);
v_messages_1804_ = lean_ctor_get(v___x_1798_, 6);
v_infoState_1805_ = lean_ctor_get(v___x_1798_, 7);
v_snapshotTasks_1806_ = lean_ctor_get(v___x_1798_, 8);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v___x_1798_, 5);
lean_dec(v_unused_1832_);
v___x_1808_ = v___x_1798_;
v_isShared_1809_ = v_isSharedCheck_1831_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_snapshotTasks_1806_);
lean_inc(v_infoState_1805_);
lean_inc(v_messages_1804_);
lean_inc(v_traceState_1803_);
lean_inc(v_auxDeclNGen_1802_);
lean_inc(v_ngen_1801_);
lean_inc(v_nextMacroScope_1800_);
lean_inc(v_env_1799_);
lean_dec(v___x_1798_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1831_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = l_Lean_Environment_setExporting(v_env_1799_, v_isExporting_1792_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 5, v___x_1793_);
lean_ctor_set(v___x_1808_, 0, v___x_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_nextMacroScope_1800_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_ngen_1801_);
lean_ctor_set(v_reuseFailAlloc_1830_, 3, v_auxDeclNGen_1802_);
lean_ctor_set(v_reuseFailAlloc_1830_, 4, v_traceState_1803_);
lean_ctor_set(v_reuseFailAlloc_1830_, 5, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1830_, 6, v_messages_1804_);
lean_ctor_set(v_reuseFailAlloc_1830_, 7, v_infoState_1805_);
lean_ctor_set(v_reuseFailAlloc_1830_, 8, v_snapshotTasks_1806_);
v___x_1812_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_mctx_1815_; lean_object* v_zetaDeltaFVarIds_1816_; lean_object* v_postponed_1817_; lean_object* v_diag_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1828_; 
v___x_1813_ = lean_st_ref_set(v___y_1791_, v___x_1812_);
v___x_1814_ = lean_st_ref_take(v___y_1794_);
v_mctx_1815_ = lean_ctor_get(v___x_1814_, 0);
v_zetaDeltaFVarIds_1816_ = lean_ctor_get(v___x_1814_, 2);
v_postponed_1817_ = lean_ctor_get(v___x_1814_, 3);
v_diag_1818_ = lean_ctor_get(v___x_1814_, 4);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v___x_1814_, 1);
lean_dec(v_unused_1829_);
v___x_1820_ = v___x_1814_;
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_diag_1818_);
lean_inc(v_postponed_1817_);
lean_inc(v_zetaDeltaFVarIds_1816_);
lean_inc(v_mctx_1815_);
lean_dec(v___x_1814_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1828_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v___x_1795_);
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_mctx_1815_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_zetaDeltaFVarIds_1816_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_postponed_1817_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_diag_1818_);
v___x_1823_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_st_ref_set(v___y_1794_, v___x_1823_);
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg___lam__0___boxed(lean_object* v___y_1833_, lean_object* v_isExporting_1834_, lean_object* v___x_1835_, lean_object* v___y_1836_, lean_object* v___x_1837_, lean_object* v_a_x3f_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v_isExporting_boxed_1840_; lean_object* v_res_1841_; 
v_isExporting_boxed_1840_ = lean_unbox(v_isExporting_1834_);
v_res_1841_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg___lam__0(v___y_1833_, v_isExporting_boxed_1840_, v___x_1835_, v___y_1836_, v___x_1837_, v_a_x3f_1838_);
lean_dec(v_a_x3f_1838_);
lean_dec(v___y_1836_);
lean_dec(v___y_1833_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg(lean_object* v_x_1842_, uint8_t v_isExporting_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; lean_object* v_env_1852_; uint8_t v_isExporting_1853_; lean_object* v___x_1854_; lean_object* v_env_1855_; lean_object* v_nextMacroScope_1856_; lean_object* v_ngen_1857_; lean_object* v_auxDeclNGen_1858_; lean_object* v_traceState_1859_; lean_object* v_messages_1860_; lean_object* v_infoState_1861_; lean_object* v_snapshotTasks_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1916_; 
v___x_1851_ = lean_st_ref_get(v___y_1849_);
v_env_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc_ref(v_env_1852_);
lean_dec(v___x_1851_);
v_isExporting_1853_ = lean_ctor_get_uint8(v_env_1852_, sizeof(void*)*8);
lean_dec_ref(v_env_1852_);
v___x_1854_ = lean_st_ref_take(v___y_1849_);
v_env_1855_ = lean_ctor_get(v___x_1854_, 0);
v_nextMacroScope_1856_ = lean_ctor_get(v___x_1854_, 1);
v_ngen_1857_ = lean_ctor_get(v___x_1854_, 2);
v_auxDeclNGen_1858_ = lean_ctor_get(v___x_1854_, 3);
v_traceState_1859_ = lean_ctor_get(v___x_1854_, 4);
v_messages_1860_ = lean_ctor_get(v___x_1854_, 6);
v_infoState_1861_ = lean_ctor_get(v___x_1854_, 7);
v_snapshotTasks_1862_ = lean_ctor_get(v___x_1854_, 8);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v___x_1854_, 5);
lean_dec(v_unused_1917_);
v___x_1864_ = v___x_1854_;
v_isShared_1865_ = v_isSharedCheck_1916_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_snapshotTasks_1862_);
lean_inc(v_infoState_1861_);
lean_inc(v_messages_1860_);
lean_inc(v_traceState_1859_);
lean_inc(v_auxDeclNGen_1858_);
lean_inc(v_ngen_1857_);
lean_inc(v_nextMacroScope_1856_);
lean_inc(v_env_1855_);
lean_dec(v___x_1854_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1916_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1866_ = l_Lean_Environment_setExporting(v_env_1855_, v_isExporting_1843_);
v___x_1867_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 5, v___x_1867_);
lean_ctor_set(v___x_1864_, 0, v___x_1866_);
v___x_1869_ = v___x_1864_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_nextMacroScope_1856_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_ngen_1857_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_auxDeclNGen_1858_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_traceState_1859_);
lean_ctor_set(v_reuseFailAlloc_1915_, 5, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1915_, 6, v_messages_1860_);
lean_ctor_set(v_reuseFailAlloc_1915_, 7, v_infoState_1861_);
lean_ctor_set(v_reuseFailAlloc_1915_, 8, v_snapshotTasks_1862_);
v___x_1869_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_mctx_1872_; lean_object* v_zetaDeltaFVarIds_1873_; lean_object* v_postponed_1874_; lean_object* v_diag_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1913_; 
v___x_1870_ = lean_st_ref_set(v___y_1849_, v___x_1869_);
v___x_1871_ = lean_st_ref_take(v___y_1847_);
v_mctx_1872_ = lean_ctor_get(v___x_1871_, 0);
v_zetaDeltaFVarIds_1873_ = lean_ctor_get(v___x_1871_, 2);
v_postponed_1874_ = lean_ctor_get(v___x_1871_, 3);
v_diag_1875_ = lean_ctor_get(v___x_1871_, 4);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v___x_1871_, 1);
lean_dec(v_unused_1914_);
v___x_1877_ = v___x_1871_;
v_isShared_1878_ = v_isSharedCheck_1913_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_diag_1875_);
lean_inc(v_postponed_1874_);
lean_inc(v_zetaDeltaFVarIds_1873_);
lean_inc(v_mctx_1872_);
lean_dec(v___x_1871_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1913_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1879_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v___x_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_mctx_1872_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_zetaDeltaFVarIds_1873_);
lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_postponed_1874_);
lean_ctor_set(v_reuseFailAlloc_1912_, 4, v_diag_1875_);
v___x_1881_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v_r_1883_; 
v___x_1882_ = lean_st_ref_set(v___y_1847_, v___x_1881_);
lean_inc(v___y_1849_);
lean_inc(v___y_1847_);
v_r_1883_ = lean_apply_7(v_x_1842_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, lean_box(0));
if (lean_obj_tag(v_r_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1900_; 
v_a_1884_ = lean_ctor_get(v_r_1883_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_r_1883_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1886_ = v_r_1883_;
v_isShared_1887_ = v_isSharedCheck_1900_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v_r_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1900_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
lean_inc(v_a_1884_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 1);
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v___x_1890_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg___lam__0(v___y_1849_, v_isExporting_1853_, v___x_1867_, v___y_1847_, v___x_1879_, v___x_1889_);
lean_dec_ref(v___x_1889_);
lean_dec(v___y_1847_);
lean_dec(v___y_1849_);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v___x_1890_, 0);
lean_dec(v_unused_1898_);
v___x_1892_ = v___x_1890_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_dec(v___x_1890_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v_a_1884_);
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1884_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
v_a_1901_ = lean_ctor_get(v_r_1883_, 0);
lean_inc(v_a_1901_);
lean_dec_ref(v_r_1883_);
v___x_1902_ = lean_box(0);
v___x_1903_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg___lam__0(v___y_1849_, v_isExporting_1853_, v___x_1867_, v___y_1847_, v___x_1879_, v___x_1902_);
lean_dec(v___y_1847_);
lean_dec(v___y_1849_);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; 
v_unused_1911_ = lean_ctor_get(v___x_1903_, 0);
lean_dec(v_unused_1911_);
v___x_1905_ = v___x_1903_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_dec(v___x_1903_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 1);
lean_ctor_set(v___x_1905_, 0, v_a_1901_);
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1901_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg___boxed(lean_object* v_x_1918_, lean_object* v_isExporting_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v_isExporting_boxed_1927_; lean_object* v_res_1928_; 
v_isExporting_boxed_1927_ = lean_unbox(v_isExporting_1919_);
v_res_1928_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg(v_x_1918_, v_isExporting_boxed_1927_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37___redArg(lean_object* v_x_1929_, uint8_t v_when_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
if (v_when_1930_ == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_apply_7(v_x_1929_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, lean_box(0));
return v___x_1938_;
}
else
{
uint8_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = 0;
v___x_1940_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg(v_x_1929_, v___x_1939_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37___redArg___boxed(lean_object* v_x_1941_, lean_object* v_when_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
uint8_t v_when_boxed_1950_; lean_object* v_res_1951_; 
v_when_boxed_1950_ = lean_unbox(v_when_1942_);
v_res_1951_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37___redArg(v_x_1941_, v_when_boxed_1950_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v_res_1951_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0(lean_object* v_k_1959_){
_start:
{
lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___closed__2));
v___x_1961_ = lean_name_eq(v_k_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
uint8_t v___x_1962_; 
v___x_1962_ = 1;
return v___x_1962_;
}
else
{
uint8_t v___x_1963_; 
v___x_1963_ = 0;
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0___boxed(lean_object* v_k_1964_){
_start:
{
uint8_t v_res_1965_; lean_object* v_r_1966_; 
v_res_1965_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__0(v_k_1964_);
lean_dec(v_k_1964_);
v_r_1966_ = lean_box(v_res_1965_);
return v_r_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32(lean_object* v_attrInstance_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___f_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___f_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; 
v___f_1976_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___closed__0));
v___x_1977_ = lean_box(0);
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = l_Lean_Syntax_getArg(v_attrInstance_1968_, v___x_1978_);
v___x_1980_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_1980_, 0, v___x_1979_);
v___f_1981_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___lam__1___boxed), 12, 5);
lean_closure_set(v___f_1981_, 0, v___x_1980_);
lean_closure_set(v___f_1981_, 1, v_attrInstance_1968_);
lean_closure_set(v___f_1981_, 2, v___f_1976_);
lean_closure_set(v___f_1981_, 3, v___x_1977_);
lean_closure_set(v___f_1981_, 4, v___x_1978_);
v___x_1982_ = 1;
v___x_1983_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37___redArg(v___f_1981_, v___x_1982_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32___boxed(lean_object* v_attrInstance_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32(v_attrInstance_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
return v_res_1992_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0(uint8_t v___y_2000_, uint8_t v_suppressElabErrors_2001_, lean_object* v_x_2002_){
_start:
{
if (lean_obj_tag(v_x_2002_) == 1)
{
lean_object* v_pre_2003_; 
v_pre_2003_ = lean_ctor_get(v_x_2002_, 0);
switch(lean_obj_tag(v_pre_2003_))
{
case 1:
{
lean_object* v_pre_2004_; 
v_pre_2004_ = lean_ctor_get(v_pre_2003_, 0);
switch(lean_obj_tag(v_pre_2004_))
{
case 0:
{
lean_object* v_str_2005_; lean_object* v_str_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_str_2005_ = lean_ctor_get(v_x_2002_, 1);
v_str_2006_ = lean_ctor_get(v_pre_2003_, 1);
v___x_2007_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__0));
v___x_2008_ = lean_string_dec_eq(v_str_2006_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__1));
v___x_2010_ = lean_string_dec_eq(v_str_2006_, v___x_2009_);
if (v___x_2010_ == 0)
{
return v___y_2000_;
}
else
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__2));
v___x_2012_ = lean_string_dec_eq(v_str_2005_, v___x_2011_);
if (v___x_2012_ == 0)
{
return v___y_2000_;
}
else
{
return v_suppressElabErrors_2001_;
}
}
}
else
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__3));
v___x_2014_ = lean_string_dec_eq(v_str_2005_, v___x_2013_);
if (v___x_2014_ == 0)
{
return v___y_2000_;
}
else
{
return v_suppressElabErrors_2001_;
}
}
}
case 1:
{
lean_object* v_pre_2015_; 
v_pre_2015_ = lean_ctor_get(v_pre_2004_, 0);
if (lean_obj_tag(v_pre_2015_) == 0)
{
lean_object* v_str_2016_; lean_object* v_str_2017_; lean_object* v_str_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_str_2016_ = lean_ctor_get(v_x_2002_, 1);
v_str_2017_ = lean_ctor_get(v_pre_2003_, 1);
v_str_2018_ = lean_ctor_get(v_pre_2004_, 1);
v___x_2019_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__4));
v___x_2020_ = lean_string_dec_eq(v_str_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
return v___y_2000_;
}
else
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__5));
v___x_2022_ = lean_string_dec_eq(v_str_2017_, v___x_2021_);
if (v___x_2022_ == 0)
{
return v___y_2000_;
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___closed__6));
v___x_2024_ = lean_string_dec_eq(v_str_2016_, v___x_2023_);
if (v___x_2024_ == 0)
{
return v___y_2000_;
}
else
{
return v_suppressElabErrors_2001_;
}
}
}
}
else
{
return v___y_2000_;
}
}
default: 
{
return v___y_2000_;
}
}
}
case 0:
{
lean_object* v_str_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_str_2025_ = lean_ctor_get(v_x_2002_, 1);
v___x_2026_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0));
v___x_2027_ = lean_string_dec_eq(v_str_2025_, v___x_2026_);
if (v___x_2027_ == 0)
{
return v___y_2000_;
}
else
{
return v_suppressElabErrors_2001_;
}
}
default: 
{
return v___y_2000_;
}
}
}
else
{
return v___y_2000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___boxed(lean_object* v___y_2028_, lean_object* v_suppressElabErrors_2029_, lean_object* v_x_2030_){
_start:
{
uint8_t v___y_56081__boxed_2031_; uint8_t v_suppressElabErrors_boxed_2032_; uint8_t v_res_2033_; lean_object* v_r_2034_; 
v___y_56081__boxed_2031_ = lean_unbox(v___y_2028_);
v_suppressElabErrors_boxed_2032_ = lean_unbox(v_suppressElabErrors_2029_);
v_res_2033_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0(v___y_56081__boxed_2031_, v_suppressElabErrors_boxed_2032_, v_x_2030_);
lean_dec(v_x_2030_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg(lean_object* v_ref_2035_, lean_object* v_msgData_2036_, uint8_t v_severity_2037_, uint8_t v_isSilent_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___y_2045_; lean_object* v___y_2046_; uint8_t v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; uint8_t v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2081_; lean_object* v___y_2082_; uint8_t v___y_2083_; uint8_t v___y_2084_; uint8_t v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2106_; lean_object* v___y_2107_; uint8_t v___y_2108_; uint8_t v___y_2109_; lean_object* v___y_2110_; uint8_t v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2117_; lean_object* v___y_2118_; uint8_t v___y_2119_; uint8_t v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; uint8_t v___y_2123_; uint8_t v___x_2128_; lean_object* v___y_2130_; uint8_t v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; uint8_t v___y_2135_; uint8_t v___y_2136_; uint8_t v___y_2138_; uint8_t v___x_2153_; 
v___x_2128_ = 2;
v___x_2153_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2037_, v___x_2128_);
if (v___x_2153_ == 0)
{
v___y_2138_ = v___x_2153_;
goto v___jp_2137_;
}
else
{
uint8_t v___x_2154_; 
lean_inc_ref(v_msgData_2036_);
v___x_2154_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2036_);
v___y_2138_ = v___x_2154_;
goto v___jp_2137_;
}
v___jp_2044_:
{
lean_object* v___x_2054_; lean_object* v_currNamespace_2055_; lean_object* v_openDecls_2056_; lean_object* v_env_2057_; lean_object* v_nextMacroScope_2058_; lean_object* v_ngen_2059_; lean_object* v_auxDeclNGen_2060_; lean_object* v_traceState_2061_; lean_object* v_cache_2062_; lean_object* v_messages_2063_; lean_object* v_infoState_2064_; lean_object* v_snapshotTasks_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2079_; 
v___x_2054_ = lean_st_ref_take(v___y_2053_);
v_currNamespace_2055_ = lean_ctor_get(v___y_2052_, 6);
lean_inc(v_currNamespace_2055_);
v_openDecls_2056_ = lean_ctor_get(v___y_2052_, 7);
lean_inc(v_openDecls_2056_);
lean_dec_ref(v___y_2052_);
v_env_2057_ = lean_ctor_get(v___x_2054_, 0);
v_nextMacroScope_2058_ = lean_ctor_get(v___x_2054_, 1);
v_ngen_2059_ = lean_ctor_get(v___x_2054_, 2);
v_auxDeclNGen_2060_ = lean_ctor_get(v___x_2054_, 3);
v_traceState_2061_ = lean_ctor_get(v___x_2054_, 4);
v_cache_2062_ = lean_ctor_get(v___x_2054_, 5);
v_messages_2063_ = lean_ctor_get(v___x_2054_, 6);
v_infoState_2064_ = lean_ctor_get(v___x_2054_, 7);
v_snapshotTasks_2065_ = lean_ctor_get(v___x_2054_, 8);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2067_ = v___x_2054_;
v_isShared_2068_ = v_isSharedCheck_2079_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_snapshotTasks_2065_);
lean_inc(v_infoState_2064_);
lean_inc(v_messages_2063_);
lean_inc(v_cache_2062_);
lean_inc(v_traceState_2061_);
lean_inc(v_auxDeclNGen_2060_);
lean_inc(v_ngen_2059_);
lean_inc(v_nextMacroScope_2058_);
lean_inc(v_env_2057_);
lean_dec(v___x_2054_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2079_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_currNamespace_2055_);
lean_ctor_set(v___x_2069_, 1, v_openDecls_2056_);
v___x_2070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___y_2049_);
v___x_2071_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2071_, 0, v___y_2046_);
lean_ctor_set(v___x_2071_, 1, v___y_2048_);
lean_ctor_set(v___x_2071_, 2, v___y_2045_);
lean_ctor_set(v___x_2071_, 3, v___y_2051_);
lean_ctor_set(v___x_2071_, 4, v___x_2070_);
lean_ctor_set_uint8(v___x_2071_, sizeof(void*)*5, v___y_2047_);
lean_ctor_set_uint8(v___x_2071_, sizeof(void*)*5 + 1, v___y_2050_);
lean_ctor_set_uint8(v___x_2071_, sizeof(void*)*5 + 2, v_isSilent_2038_);
v___x_2072_ = l_Lean_MessageLog_add(v___x_2071_, v_messages_2063_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 6, v___x_2072_);
v___x_2074_ = v___x_2067_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_env_2057_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_nextMacroScope_2058_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_ngen_2059_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_auxDeclNGen_2060_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v_traceState_2061_);
lean_ctor_set(v_reuseFailAlloc_2078_, 5, v_cache_2062_);
lean_ctor_set(v_reuseFailAlloc_2078_, 6, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2078_, 7, v_infoState_2064_);
lean_ctor_set(v_reuseFailAlloc_2078_, 8, v_snapshotTasks_2065_);
v___x_2074_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_st_ref_set(v___y_2053_, v___x_2074_);
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
}
}
v___jp_2080_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2104_; 
v___x_2089_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2036_);
v___x_2090_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(v___x_2089_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2104_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2104_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_inc_ref(v___y_2087_);
v___x_2095_ = l_Lean_FileMap_toPosition(v___y_2087_, v___y_2086_);
lean_dec(v___y_2086_);
v___x_2096_ = l_Lean_FileMap_toPosition(v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
v___x_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
v___x_2098_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___closed__1));
if (v___y_2083_ == 0)
{
lean_del_object(v___x_2093_);
lean_dec_ref(v___y_2081_);
v___y_2045_ = v___x_2097_;
v___y_2046_ = v___y_2082_;
v___y_2047_ = v___y_2084_;
v___y_2048_ = v___x_2095_;
v___y_2049_ = v_a_2091_;
v___y_2050_ = v___y_2085_;
v___y_2051_ = v___x_2098_;
v___y_2052_ = v___y_2041_;
v___y_2053_ = v___y_2042_;
goto v___jp_2044_;
}
else
{
uint8_t v___x_2099_; 
lean_inc(v_a_2091_);
v___x_2099_ = l_Lean_MessageData_hasTag(v___y_2081_, v_a_2091_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec_ref(v___x_2097_);
lean_dec_ref(v___x_2095_);
lean_dec(v_a_2091_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v___y_2041_);
v___x_2100_ = lean_box(0);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2100_);
v___x_2102_ = v___x_2093_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
else
{
lean_del_object(v___x_2093_);
v___y_2045_ = v___x_2097_;
v___y_2046_ = v___y_2082_;
v___y_2047_ = v___y_2084_;
v___y_2048_ = v___x_2095_;
v___y_2049_ = v_a_2091_;
v___y_2050_ = v___y_2085_;
v___y_2051_ = v___x_2098_;
v___y_2052_ = v___y_2041_;
v___y_2053_ = v___y_2042_;
goto v___jp_2044_;
}
}
}
}
v___jp_2105_:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_Syntax_getTailPos_x3f(v___y_2110_, v___y_2109_);
lean_dec(v___y_2110_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_inc(v___y_2113_);
v___y_2081_ = v___y_2106_;
v___y_2082_ = v___y_2107_;
v___y_2083_ = v___y_2108_;
v___y_2084_ = v___y_2109_;
v___y_2085_ = v___y_2111_;
v___y_2086_ = v___y_2113_;
v___y_2087_ = v___y_2112_;
v___y_2088_ = v___y_2113_;
goto v___jp_2080_;
}
else
{
lean_object* v_val_2115_; 
v_val_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_val_2115_);
lean_dec_ref(v___x_2114_);
v___y_2081_ = v___y_2106_;
v___y_2082_ = v___y_2107_;
v___y_2083_ = v___y_2108_;
v___y_2084_ = v___y_2109_;
v___y_2085_ = v___y_2111_;
v___y_2086_ = v___y_2113_;
v___y_2087_ = v___y_2112_;
v___y_2088_ = v_val_2115_;
goto v___jp_2080_;
}
}
v___jp_2116_:
{
lean_object* v_ref_2124_; lean_object* v___x_2125_; 
v_ref_2124_ = l_Lean_replaceRef(v_ref_2035_, v___y_2122_);
lean_dec(v___y_2122_);
v___x_2125_ = l_Lean_Syntax_getPos_x3f(v_ref_2124_, v___y_2120_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___y_2106_ = v___y_2117_;
v___y_2107_ = v___y_2118_;
v___y_2108_ = v___y_2119_;
v___y_2109_ = v___y_2120_;
v___y_2110_ = v_ref_2124_;
v___y_2111_ = v___y_2123_;
v___y_2112_ = v___y_2121_;
v___y_2113_ = v___x_2126_;
goto v___jp_2105_;
}
else
{
lean_object* v_val_2127_; 
v_val_2127_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_val_2127_);
lean_dec_ref(v___x_2125_);
v___y_2106_ = v___y_2117_;
v___y_2107_ = v___y_2118_;
v___y_2108_ = v___y_2119_;
v___y_2109_ = v___y_2120_;
v___y_2110_ = v_ref_2124_;
v___y_2111_ = v___y_2123_;
v___y_2112_ = v___y_2121_;
v___y_2113_ = v_val_2127_;
goto v___jp_2105_;
}
}
v___jp_2129_:
{
if (v___y_2136_ == 0)
{
v___y_2117_ = v___y_2132_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___y_2131_;
v___y_2120_ = v___y_2135_;
v___y_2121_ = v___y_2134_;
v___y_2122_ = v___y_2133_;
v___y_2123_ = v_severity_2037_;
goto v___jp_2116_;
}
else
{
v___y_2117_ = v___y_2132_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___y_2131_;
v___y_2120_ = v___y_2135_;
v___y_2121_ = v___y_2134_;
v___y_2122_ = v___y_2133_;
v___y_2123_ = v___x_2128_;
goto v___jp_2116_;
}
}
v___jp_2137_:
{
if (v___y_2138_ == 0)
{
lean_object* v_fileName_2139_; lean_object* v_fileMap_2140_; lean_object* v_options_2141_; lean_object* v_ref_2142_; uint8_t v_suppressElabErrors_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___f_2146_; uint8_t v___x_2147_; uint8_t v___x_2148_; 
v_fileName_2139_ = lean_ctor_get(v___y_2041_, 0);
v_fileMap_2140_ = lean_ctor_get(v___y_2041_, 1);
v_options_2141_ = lean_ctor_get(v___y_2041_, 2);
v_ref_2142_ = lean_ctor_get(v___y_2041_, 5);
v_suppressElabErrors_2143_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*14 + 1);
v___x_2144_ = lean_box(v___y_2138_);
v___x_2145_ = lean_box(v_suppressElabErrors_2143_);
v___f_2146_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2146_, 0, v___x_2144_);
lean_closure_set(v___f_2146_, 1, v___x_2145_);
v___x_2147_ = 1;
v___x_2148_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2037_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_inc_ref(v_fileMap_2140_);
lean_inc(v_ref_2142_);
lean_inc_ref(v_fileName_2139_);
v___y_2130_ = v_fileName_2139_;
v___y_2131_ = v_suppressElabErrors_2143_;
v___y_2132_ = v___f_2146_;
v___y_2133_ = v_ref_2142_;
v___y_2134_ = v_fileMap_2140_;
v___y_2135_ = v___y_2138_;
v___y_2136_ = v___x_2148_;
goto v___jp_2129_;
}
else
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = l_Lean_warningAsError;
v___x_2150_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_options_2141_, v___x_2149_);
lean_inc_ref(v_fileMap_2140_);
lean_inc(v_ref_2142_);
lean_inc_ref(v_fileName_2139_);
v___y_2130_ = v_fileName_2139_;
v___y_2131_ = v_suppressElabErrors_2143_;
v___y_2132_ = v___f_2146_;
v___y_2133_ = v_ref_2142_;
v___y_2134_ = v_fileMap_2140_;
v___y_2135_ = v___y_2138_;
v___y_2136_ = v___x_2150_;
goto v___jp_2129_;
}
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_msgData_2036_);
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg___boxed(lean_object* v_ref_2155_, lean_object* v_msgData_2156_, lean_object* v_severity_2157_, lean_object* v_isSilent_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
uint8_t v_severity_boxed_2164_; uint8_t v_isSilent_boxed_2165_; lean_object* v_res_2166_; 
v_severity_boxed_2164_ = lean_unbox(v_severity_2157_);
v_isSilent_boxed_2165_ = lean_unbox(v_isSilent_2158_);
v_res_2166_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg(v_ref_2155_, v_msgData_2156_, v_severity_boxed_2164_, v_isSilent_boxed_2165_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v_ref_2155_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39(lean_object* v_ref_2167_, lean_object* v_msgData_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
uint8_t v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = 2;
v___x_2177_ = 0;
v___x_2178_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg(v_ref_2167_, v_msgData_2168_, v___x_2176_, v___x_2177_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39___boxed(lean_object* v_ref_2179_, lean_object* v_msgData_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39(v_ref_2179_, v_msgData_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v_ref_2179_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40_spec__45(lean_object* v_msgData_2189_, uint8_t v_severity_2190_, uint8_t v_isSilent_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_ref_2199_; lean_object* v___x_2200_; 
v_ref_2199_ = lean_ctor_get(v___y_2196_, 5);
lean_inc(v_ref_2199_);
v___x_2200_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg(v_ref_2199_, v_msgData_2189_, v_severity_2190_, v_isSilent_2191_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v_ref_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40_spec__45___boxed(lean_object* v_msgData_2201_, lean_object* v_severity_2202_, lean_object* v_isSilent_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
uint8_t v_severity_boxed_2211_; uint8_t v_isSilent_boxed_2212_; lean_object* v_res_2213_; 
v_severity_boxed_2211_ = lean_unbox(v_severity_2202_);
v_isSilent_boxed_2212_ = lean_unbox(v_isSilent_2203_);
v_res_2213_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40_spec__45(v_msgData_2201_, v_severity_boxed_2211_, v_isSilent_boxed_2212_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40(lean_object* v_msgData_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
uint8_t v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; 
v___x_2222_ = 2;
v___x_2223_ = 0;
v___x_2224_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40_spec__45(v_msgData_2214_, v___x_2222_, v___x_2223_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40___boxed(lean_object* v_msgData_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40(v_msgData_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
return v_res_2233_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__1(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__0));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33(lean_object* v_ex_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
if (lean_obj_tag(v_ex_2237_) == 0)
{
lean_object* v_ref_2245_; lean_object* v_msg_2246_; lean_object* v___x_2247_; 
v_ref_2245_ = lean_ctor_get(v_ex_2237_, 0);
lean_inc(v_ref_2245_);
v_msg_2246_ = lean_ctor_get(v_ex_2237_, 1);
lean_inc_ref(v_msg_2246_);
lean_dec_ref(v_ex_2237_);
v___x_2247_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39(v_ref_2245_, v_msg_2246_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v_ref_2245_);
return v___x_2247_;
}
else
{
lean_object* v_id_2248_; uint8_t v___y_2250_; uint8_t v___x_2272_; 
v_id_2248_ = lean_ctor_get(v_ex_2237_, 0);
lean_inc(v_id_2248_);
v___x_2272_ = l_Lean_Elab_isAbortExceptionId(v_id_2248_);
if (v___x_2272_ == 0)
{
uint8_t v___x_2273_; 
v___x_2273_ = l_Lean_Exception_isInterrupt(v_ex_2237_);
lean_dec_ref(v_ex_2237_);
v___y_2250_ = v___x_2273_;
goto v___jp_2249_;
}
else
{
lean_dec_ref(v_ex_2237_);
v___y_2250_ = v___x_2272_;
goto v___jp_2249_;
}
v___jp_2249_:
{
if (v___y_2250_ == 0)
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_InternalExceptionId_getName(v_id_2248_);
lean_dec(v_id_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___closed__1);
v___x_2254_ = l_Lean_MessageData_ofName(v_a_2252_);
v___x_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__40(v___x_2255_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
return v___x_2256_;
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2269_; 
v_a_2257_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2259_ = v___x_2251_;
v_isShared_2260_ = v_isSharedCheck_2269_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2251_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2269_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_ref_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
v_ref_2261_ = lean_ctor_get(v___y_2242_, 5);
lean_inc(v_ref_2261_);
lean_dec_ref(v___y_2242_);
v___x_2262_ = lean_io_error_to_string(v_a_2257_);
v___x_2263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = l_Lean_MessageData_ofFormat(v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v_ref_2261_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2265_);
v___x_2267_ = v___x_2259_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_id_2248_);
lean_dec_ref(v___y_2242_);
v___x_2270_ = lean_box(0);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33___boxed(lean_object* v_ex_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33(v_ex_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__34(lean_object* v_as_2283_, size_t v_sz_2284_, size_t v_i_2285_, lean_object* v_b_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_snd_2295_; uint8_t v___x_2299_; 
v___x_2299_ = lean_usize_dec_lt(v_i_2285_, v_sz_2284_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; 
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_b_2286_);
return v___x_2300_;
}
else
{
lean_object* v_fileName_2301_; lean_object* v_fileMap_2302_; lean_object* v_options_2303_; lean_object* v_currRecDepth_2304_; lean_object* v_maxRecDepth_2305_; lean_object* v_ref_2306_; lean_object* v_currNamespace_2307_; lean_object* v_openDecls_2308_; lean_object* v_initHeartbeats_2309_; lean_object* v_maxHeartbeats_2310_; lean_object* v_quotContext_2311_; lean_object* v_currMacroScope_2312_; uint8_t v_diag_2313_; lean_object* v_cancelTk_x3f_2314_; uint8_t v_suppressElabErrors_2315_; lean_object* v_inheritedTraceOptions_2316_; lean_object* v_a_2317_; lean_object* v_ref_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_fileName_2301_ = lean_ctor_get(v___y_2291_, 0);
v_fileMap_2302_ = lean_ctor_get(v___y_2291_, 1);
v_options_2303_ = lean_ctor_get(v___y_2291_, 2);
v_currRecDepth_2304_ = lean_ctor_get(v___y_2291_, 3);
v_maxRecDepth_2305_ = lean_ctor_get(v___y_2291_, 4);
v_ref_2306_ = lean_ctor_get(v___y_2291_, 5);
v_currNamespace_2307_ = lean_ctor_get(v___y_2291_, 6);
v_openDecls_2308_ = lean_ctor_get(v___y_2291_, 7);
v_initHeartbeats_2309_ = lean_ctor_get(v___y_2291_, 8);
v_maxHeartbeats_2310_ = lean_ctor_get(v___y_2291_, 9);
v_quotContext_2311_ = lean_ctor_get(v___y_2291_, 10);
v_currMacroScope_2312_ = lean_ctor_get(v___y_2291_, 11);
v_diag_2313_ = lean_ctor_get_uint8(v___y_2291_, sizeof(void*)*14);
v_cancelTk_x3f_2314_ = lean_ctor_get(v___y_2291_, 12);
v_suppressElabErrors_2315_ = lean_ctor_get_uint8(v___y_2291_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2316_ = lean_ctor_get(v___y_2291_, 13);
v_a_2317_ = lean_array_uget_borrowed(v_as_2283_, v_i_2285_);
v_ref_2318_ = l_Lean_replaceRef(v_a_2317_, v_ref_2306_);
lean_inc_ref(v_inheritedTraceOptions_2316_);
lean_inc(v_cancelTk_x3f_2314_);
lean_inc(v_currMacroScope_2312_);
lean_inc(v_quotContext_2311_);
lean_inc(v_maxHeartbeats_2310_);
lean_inc(v_initHeartbeats_2309_);
lean_inc(v_openDecls_2308_);
lean_inc(v_currNamespace_2307_);
lean_inc(v_maxRecDepth_2305_);
lean_inc(v_currRecDepth_2304_);
lean_inc_ref(v_options_2303_);
lean_inc_ref(v_fileMap_2302_);
lean_inc_ref(v_fileName_2301_);
v___x_2319_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2319_, 0, v_fileName_2301_);
lean_ctor_set(v___x_2319_, 1, v_fileMap_2302_);
lean_ctor_set(v___x_2319_, 2, v_options_2303_);
lean_ctor_set(v___x_2319_, 3, v_currRecDepth_2304_);
lean_ctor_set(v___x_2319_, 4, v_maxRecDepth_2305_);
lean_ctor_set(v___x_2319_, 5, v_ref_2318_);
lean_ctor_set(v___x_2319_, 6, v_currNamespace_2307_);
lean_ctor_set(v___x_2319_, 7, v_openDecls_2308_);
lean_ctor_set(v___x_2319_, 8, v_initHeartbeats_2309_);
lean_ctor_set(v___x_2319_, 9, v_maxHeartbeats_2310_);
lean_ctor_set(v___x_2319_, 10, v_quotContext_2311_);
lean_ctor_set(v___x_2319_, 11, v_currMacroScope_2312_);
lean_ctor_set(v___x_2319_, 12, v_cancelTk_x3f_2314_);
lean_ctor_set(v___x_2319_, 13, v_inheritedTraceOptions_2316_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*14, v_diag_2313_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*14 + 1, v_suppressElabErrors_2315_);
lean_inc(v___y_2292_);
lean_inc(v___y_2290_);
lean_inc_ref(v___y_2289_);
lean_inc(v___y_2288_);
lean_inc_ref(v___y_2287_);
lean_inc(v_a_2317_);
v___x_2320_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32(v_a_2317_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___x_2319_, v___y_2292_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = lean_array_push(v_b_2286_, v_a_2321_);
v_snd_2295_ = v___x_2322_;
goto v___jp_2294_;
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2343_; 
v_a_2323_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2325_ = v___x_2320_;
v_isShared_2326_ = v_isSharedCheck_2343_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2320_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2343_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
uint8_t v___y_2328_; uint8_t v___x_2341_; 
v___x_2341_ = l_Lean_Exception_isInterrupt(v_a_2323_);
if (v___x_2341_ == 0)
{
uint8_t v___x_2342_; 
lean_inc(v_a_2323_);
v___x_2342_ = l_Lean_Exception_isRuntime(v_a_2323_);
v___y_2328_ = v___x_2342_;
goto v___jp_2327_;
}
else
{
v___y_2328_ = v___x_2341_;
goto v___jp_2327_;
}
v___jp_2327_:
{
if (v___y_2328_ == 0)
{
lean_object* v___x_2329_; 
lean_del_object(v___x_2325_);
lean_inc_ref(v___y_2291_);
v___x_2329_ = l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33(v_a_2323_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_dec_ref(v___x_2329_);
v_snd_2295_ = v_b_2286_;
goto v___jp_2294_;
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec_ref(v_b_2286_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v___x_2339_; 
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec_ref(v_b_2286_);
if (v_isShared_2326_ == 0)
{
v___x_2339_ = v___x_2325_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2323_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
}
v___jp_2294_:
{
size_t v___x_2296_; size_t v___x_2297_; 
v___x_2296_ = ((size_t)1ULL);
v___x_2297_ = lean_usize_add(v_i_2285_, v___x_2296_);
v_i_2285_ = v___x_2297_;
v_b_2286_ = v_snd_2295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__34___boxed(lean_object* v_as_2344_, lean_object* v_sz_2345_, lean_object* v_i_2346_, lean_object* v_b_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
size_t v_sz_boxed_2355_; size_t v_i_boxed_2356_; lean_object* v_res_2357_; 
v_sz_boxed_2355_ = lean_unbox_usize(v_sz_2345_);
lean_dec(v_sz_2345_);
v_i_boxed_2356_ = lean_unbox_usize(v_i_2346_);
lean_dec(v_i_2346_);
v_res_2357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__34(v_as_2344_, v_sz_boxed_2355_, v_i_boxed_2356_, v_b_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec_ref(v_as_2344_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23(lean_object* v_attrInstances_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_attrs_2368_; size_t v_sz_2369_; size_t v___x_2370_; lean_object* v___x_2371_; 
v_attrs_2368_ = ((lean_object*)(l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23___closed__0));
v_sz_2369_ = lean_array_size(v_attrInstances_2360_);
v___x_2370_ = ((size_t)0ULL);
v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__34(v_attrInstances_2360_, v_sz_2369_, v___x_2370_, v_attrs_2368_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23___boxed(lean_object* v_attrInstances_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23(v_attrInstances_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec_ref(v_attrInstances_2372_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(lean_object* v_stx_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2389_ = lean_unsigned_to_nat(1u);
v___x_2390_ = l_Lean_Syntax_getArg(v_stx_2381_, v___x_2389_);
v___x_2391_ = l_Lean_Syntax_getSepArgs(v___x_2390_);
lean_dec(v___x_2390_);
v___x_2392_ = l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23(v___x_2391_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec_ref(v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9___boxed(lean_object* v_stx_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(v_stx_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v_stx_2393_);
return v_res_2401_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__0));
v___x_2404_ = l_Lean_stringToMessageData(v___x_2403_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__2));
v___x_2407_ = l_Lean_stringToMessageData(v___x_2406_);
return v___x_2407_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__4));
v___x_2410_ = l_Lean_stringToMessageData(v___x_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5(lean_object* v_addInfo_2411_, lean_object* v_declName_2412_, uint8_t v___x_2413_, lean_object* v___f_2414_, uint8_t v___x_2415_, lean_object* v_env_2416_, lean_object* v___f_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v_declName_2412_);
v___x_2425_ = lean_apply_8(v_addInfo_2411_, v_declName_2412_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, lean_box(0));
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v___x_2426_; 
lean_dec_ref(v___x_2425_);
lean_inc(v_declName_2412_);
v___x_2426_ = lean_private_to_user_name(v_declName_2412_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2427_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2428_ = l_Lean_MessageData_ofConstName(v_declName_2412_, v___x_2413_);
v___x_2429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2431_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
return v___x_2432_;
}
else
{
lean_object* v_val_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_dec(v_declName_2412_);
v_val_2433_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_val_2433_);
lean_dec_ref(v___x_2426_);
v___x_2434_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5);
v___x_2435_ = l_Lean_MessageData_ofConstName(v_val_2433_, v___x_2413_);
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2438_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
return v___x_2439_;
}
}
else
{
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_declName_2412_);
return v___x_2425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___boxed(lean_object* v_addInfo_2440_, lean_object* v_declName_2441_, lean_object* v___x_2442_, lean_object* v___f_2443_, lean_object* v___x_2444_, lean_object* v_env_2445_, lean_object* v___f_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_56683__boxed_2454_; uint8_t v___x_56685__boxed_2455_; lean_object* v_res_2456_; 
v___x_56683__boxed_2454_ = lean_unbox(v___x_2442_);
v___x_56685__boxed_2455_ = lean_unbox(v___x_2444_);
v_res_2456_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5(v_addInfo_2440_, v_declName_2441_, v___x_56683__boxed_2454_, v___f_2443_, v___x_56685__boxed_2455_, v_env_2445_, v___f_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec_ref(v___f_2446_);
lean_dec_ref(v_env_2445_);
lean_dec_ref(v___f_2443_);
return v_res_2456_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__0));
v___x_2459_ = l_Lean_stringToMessageData(v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3(lean_object* v___f_2460_, lean_object* v_declName_2461_, uint8_t v___x_2462_, lean_object* v_env_2463_, lean_object* v_____do__lift_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
uint8_t v___y_2473_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
lean_inc(v_declName_2461_);
v___x_2482_ = l_Lean_privateToUserName(v_declName_2461_);
lean_inc_ref(v_env_2463_);
v___x_2483_ = lean_is_reserved_name(v_env_2463_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
lean_inc(v_declName_2461_);
v___x_2484_ = l_Lean_mkPrivateName(v_____do__lift_2464_, v_declName_2461_);
v___x_2485_ = lean_is_reserved_name(v_env_2463_, v___x_2484_);
v___y_2473_ = v___x_2485_;
goto v___jp_2472_;
}
else
{
lean_dec_ref(v_env_2463_);
v___y_2473_ = v___x_2483_;
goto v___jp_2472_;
}
v___jp_2472_:
{
if (v___y_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_dec(v_declName_2461_);
v___x_2474_ = lean_box(0);
v___x_2475_ = lean_apply_8(v___f_2460_, v___x_2474_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, lean_box(0));
return v___x_2475_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec_ref(v___f_2460_);
v___x_2476_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2477_ = l_Lean_MessageData_ofConstName(v_declName_2461_, v___x_2462_);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1);
v___x_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2480_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
return v___x_2481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___boxed(lean_object* v___f_2486_, lean_object* v_declName_2487_, lean_object* v___x_2488_, lean_object* v_env_2489_, lean_object* v_____do__lift_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
uint8_t v___x_56771__boxed_2498_; lean_object* v_res_2499_; 
v___x_56771__boxed_2498_ = lean_unbox(v___x_2488_);
v_res_2499_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3(v___f_2486_, v_declName_2487_, v___x_56771__boxed_2498_, v_env_2489_, v_____do__lift_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec_ref(v_____do__lift_2490_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(lean_object* v_t_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v_infoState_2504_; uint8_t v_enabled_2505_; 
v___x_2503_ = lean_st_ref_get(v___y_2501_);
v_infoState_2504_ = lean_ctor_get(v___x_2503_, 7);
lean_inc_ref(v_infoState_2504_);
lean_dec(v___x_2503_);
v_enabled_2505_ = lean_ctor_get_uint8(v_infoState_2504_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2504_);
if (v_enabled_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec_ref(v_t_2500_);
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; lean_object* v_infoState_2509_; lean_object* v_env_2510_; lean_object* v_nextMacroScope_2511_; lean_object* v_ngen_2512_; lean_object* v_auxDeclNGen_2513_; lean_object* v_traceState_2514_; lean_object* v_cache_2515_; lean_object* v_messages_2516_; lean_object* v_snapshotTasks_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2539_; 
v___x_2508_ = lean_st_ref_take(v___y_2501_);
v_infoState_2509_ = lean_ctor_get(v___x_2508_, 7);
v_env_2510_ = lean_ctor_get(v___x_2508_, 0);
v_nextMacroScope_2511_ = lean_ctor_get(v___x_2508_, 1);
v_ngen_2512_ = lean_ctor_get(v___x_2508_, 2);
v_auxDeclNGen_2513_ = lean_ctor_get(v___x_2508_, 3);
v_traceState_2514_ = lean_ctor_get(v___x_2508_, 4);
v_cache_2515_ = lean_ctor_get(v___x_2508_, 5);
v_messages_2516_ = lean_ctor_get(v___x_2508_, 6);
v_snapshotTasks_2517_ = lean_ctor_get(v___x_2508_, 8);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2519_ = v___x_2508_;
v_isShared_2520_ = v_isSharedCheck_2539_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_snapshotTasks_2517_);
lean_inc(v_infoState_2509_);
lean_inc(v_messages_2516_);
lean_inc(v_cache_2515_);
lean_inc(v_traceState_2514_);
lean_inc(v_auxDeclNGen_2513_);
lean_inc(v_ngen_2512_);
lean_inc(v_nextMacroScope_2511_);
lean_inc(v_env_2510_);
lean_dec(v___x_2508_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2539_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
uint8_t v_enabled_2521_; lean_object* v_assignment_2522_; lean_object* v_lazyAssignment_2523_; lean_object* v_trees_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2538_; 
v_enabled_2521_ = lean_ctor_get_uint8(v_infoState_2509_, sizeof(void*)*3);
v_assignment_2522_ = lean_ctor_get(v_infoState_2509_, 0);
v_lazyAssignment_2523_ = lean_ctor_get(v_infoState_2509_, 1);
v_trees_2524_ = lean_ctor_get(v_infoState_2509_, 2);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_infoState_2509_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2526_ = v_infoState_2509_;
v_isShared_2527_ = v_isSharedCheck_2538_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_trees_2524_);
lean_inc(v_lazyAssignment_2523_);
lean_inc(v_assignment_2522_);
lean_dec(v_infoState_2509_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2538_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = l_Lean_PersistentArray_push___redArg(v_trees_2524_, v_t_2500_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 2, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_assignment_2522_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_lazyAssignment_2523_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v___x_2528_);
lean_ctor_set_uint8(v_reuseFailAlloc_2537_, sizeof(void*)*3, v_enabled_2521_);
v___x_2530_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2532_; 
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 7, v___x_2530_);
v___x_2532_ = v___x_2519_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_env_2510_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_nextMacroScope_2511_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_ngen_2512_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_auxDeclNGen_2513_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_traceState_2514_);
lean_ctor_set(v_reuseFailAlloc_2536_, 5, v_cache_2515_);
lean_ctor_set(v_reuseFailAlloc_2536_, 6, v_messages_2516_);
lean_ctor_set(v_reuseFailAlloc_2536_, 7, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2536_, 8, v_snapshotTasks_2517_);
v___x_2532_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_st_ref_set(v___y_2501_, v___x_2532_);
v___x_2534_ = lean_box(0);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
return v___x_2535_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_t_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v_t_2540_, v___y_2541_);
lean_dec(v___y_2541_);
return v_res_2543_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_unsigned_to_nat(32u);
v___x_2545_ = lean_mk_empty_array_with_capacity(v___x_2544_);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1(void){
_start:
{
size_t v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2547_ = ((size_t)5ULL);
v___x_2548_ = lean_unsigned_to_nat(0u);
v___x_2549_ = lean_unsigned_to_nat(32u);
v___x_2550_ = lean_mk_empty_array_with_capacity(v___x_2549_);
v___x_2551_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0);
v___x_2552_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
lean_ctor_set(v___x_2552_, 1, v___x_2550_);
lean_ctor_set(v___x_2552_, 2, v___x_2548_);
lean_ctor_set(v___x_2552_, 3, v___x_2548_);
lean_ctor_set_usize(v___x_2552_, 4, v___x_2547_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(lean_object* v_t_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; lean_object* v_infoState_2562_; uint8_t v_enabled_2563_; 
v___x_2561_ = lean_st_ref_get(v___y_2559_);
v_infoState_2562_ = lean_ctor_get(v___x_2561_, 7);
lean_inc_ref(v_infoState_2562_);
lean_dec(v___x_2561_);
v_enabled_2563_ = lean_ctor_get_uint8(v_infoState_2562_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2562_);
if (v_enabled_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec_ref(v_t_2553_);
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_t_2553_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v___x_2567_, v___y_2559_);
return v___x_2568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___boxed(lean_object* v_t_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(v_t_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__4(lean_object* v_a_2578_, lean_object* v_a_2579_){
_start:
{
if (lean_obj_tag(v_a_2578_) == 0)
{
lean_object* v___x_2580_; 
v___x_2580_ = l_List_reverse___redArg(v_a_2579_);
return v___x_2580_;
}
else
{
lean_object* v_head_2581_; lean_object* v_tail_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2591_; 
v_head_2581_ = lean_ctor_get(v_a_2578_, 0);
v_tail_2582_ = lean_ctor_get(v_a_2578_, 1);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_a_2578_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2584_ = v_a_2578_;
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_tail_2582_);
lean_inc(v_head_2581_);
lean_dec(v_a_2578_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = l_Lean_mkLevelParam(v_head_2581_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 1, v_a_2579_);
lean_ctor_set(v___x_2584_, 0, v___x_2586_);
v___x_2588_ = v___x_2584_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_a_2579_);
v___x_2588_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
v_a_2578_ = v_tail_2582_;
v_a_2579_ = v___x_2588_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__0(void){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2592_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__1(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__0);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
return v___x_2594_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__2(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__1);
v___x_2596_ = lean_unsigned_to_nat(0u);
v___x_2597_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
lean_ctor_set(v___x_2597_, 2, v___x_2596_);
lean_ctor_set(v___x_2597_, 3, v___x_2595_);
lean_ctor_set(v___x_2597_, 4, v___x_2595_);
lean_ctor_set(v___x_2597_, 5, v___x_2595_);
lean_ctor_set(v___x_2597_, 6, v___x_2595_);
lean_ctor_set(v___x_2597_, 7, v___x_2595_);
lean_ctor_set(v___x_2597_, 8, v___x_2595_);
return v___x_2597_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__3(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_unsigned_to_nat(32u);
v___x_2599_ = lean_mk_empty_array_with_capacity(v___x_2598_);
v___x_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__4(void){
_start:
{
size_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2601_ = ((size_t)5ULL);
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = lean_unsigned_to_nat(32u);
v___x_2604_ = lean_mk_empty_array_with_capacity(v___x_2603_);
v___x_2605_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__3);
v___x_2606_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v___x_2604_);
lean_ctor_set(v___x_2606_, 2, v___x_2602_);
lean_ctor_set(v___x_2606_, 3, v___x_2602_);
lean_ctor_set_usize(v___x_2606_, 4, v___x_2601_);
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__5(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2607_ = lean_box(1);
v___x_2608_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__4);
v___x_2609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__1);
v___x_2610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2608_);
lean_ctor_set(v___x_2610_, 2, v___x_2607_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__7(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__6));
v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__9(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__8));
v___x_2616_ = l_Lean_stringToMessageData(v___x_2615_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__11(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__10));
v___x_2619_ = l_Lean_stringToMessageData(v___x_2618_);
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__13(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__12));
v___x_2622_ = l_Lean_stringToMessageData(v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__15(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__14));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__17(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__16));
v___x_2628_ = l_Lean_stringToMessageData(v___x_2627_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__19(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__18));
v___x_2631_ = l_Lean_stringToMessageData(v___x_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg(lean_object* v_msg_2632_, lean_object* v_declHint_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v___x_2636_; lean_object* v_env_2637_; uint8_t v___x_2638_; 
v___x_2636_ = lean_st_ref_get(v___y_2634_);
v_env_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc_ref(v_env_2637_);
lean_dec(v___x_2636_);
v___x_2638_ = l_Lean_Name_isAnonymous(v_declHint_2633_);
if (v___x_2638_ == 0)
{
uint8_t v_isExporting_2639_; 
v_isExporting_2639_ = lean_ctor_get_uint8(v_env_2637_, sizeof(void*)*8);
if (v_isExporting_2639_ == 0)
{
lean_object* v___x_2640_; 
lean_dec_ref(v_env_2637_);
lean_dec(v_declHint_2633_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_msg_2632_);
return v___x_2640_;
}
else
{
lean_object* v___x_2641_; uint8_t v___x_2642_; 
lean_inc_ref(v_env_2637_);
v___x_2641_ = l_Lean_Environment_setExporting(v_env_2637_, v___x_2638_);
lean_inc(v_declHint_2633_);
lean_inc_ref(v___x_2641_);
v___x_2642_ = l_Lean_Environment_contains(v___x_2641_, v_declHint_2633_, v_isExporting_2639_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; 
lean_dec_ref(v___x_2641_);
lean_dec_ref(v_env_2637_);
lean_dec(v_declHint_2633_);
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_msg_2632_);
return v___x_2643_;
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v_c_2649_; lean_object* v___x_2650_; 
v___x_2644_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__2);
v___x_2645_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__5);
v___x_2646_ = l_Lean_Options_empty;
v___x_2647_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2641_);
lean_ctor_set(v___x_2647_, 1, v___x_2644_);
lean_ctor_set(v___x_2647_, 2, v___x_2645_);
lean_ctor_set(v___x_2647_, 3, v___x_2646_);
lean_inc(v_declHint_2633_);
v___x_2648_ = l_Lean_MessageData_ofConstName(v_declHint_2633_, v___x_2638_);
v_c_2649_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2649_, 0, v___x_2647_);
lean_ctor_set(v_c_2649_, 1, v___x_2648_);
v___x_2650_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2637_, v_declHint_2633_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec_ref(v_env_2637_);
lean_dec(v_declHint_2633_);
v___x_2651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__7);
v___x_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
lean_ctor_set(v___x_2652_, 1, v_c_2649_);
v___x_2653_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__9);
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = l_Lean_MessageData_note(v___x_2654_);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v_msg_2632_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
return v___x_2657_;
}
else
{
lean_object* v_val_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2693_; 
v_val_2658_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2660_ = v___x_2650_;
v_isShared_2661_ = v_isSharedCheck_2693_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_val_2658_);
lean_dec(v___x_2650_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2693_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v_mod_2665_; uint8_t v___x_2666_; 
v___x_2662_ = lean_box(0);
v___x_2663_ = l_Lean_Environment_header(v_env_2637_);
lean_dec_ref(v_env_2637_);
v___x_2664_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2663_);
v_mod_2665_ = lean_array_get(v___x_2662_, v___x_2664_, v_val_2658_);
lean_dec(v_val_2658_);
lean_dec_ref(v___x_2664_);
v___x_2666_ = l_Lean_isPrivateName(v_declHint_2633_);
lean_dec(v_declHint_2633_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2678_; 
v___x_2667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__11);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
lean_ctor_set(v___x_2668_, 1, v_c_2649_);
v___x_2669_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__13);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = l_Lean_MessageData_ofName(v_mod_2665_);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__15);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = l_Lean_MessageData_note(v___x_2674_);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v_msg_2632_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set_tag(v___x_2660_, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2676_);
v___x_2678_ = v___x_2660_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__7);
v___x_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
lean_ctor_set(v___x_2681_, 1, v_c_2649_);
v___x_2682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__17);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = l_Lean_MessageData_ofName(v_mod_2665_);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__19);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = l_Lean_MessageData_note(v___x_2687_);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v_msg_2632_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set_tag(v___x_2660_, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2689_);
v___x_2691_ = v___x_2660_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2694_; 
lean_dec_ref(v_env_2637_);
lean_dec(v_declHint_2633_);
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_msg_2632_);
return v___x_2694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___boxed(lean_object* v_msg_2695_, lean_object* v_declHint_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg(v_msg_2695_, v_declHint_2696_, v___y_2697_);
lean_dec(v___y_2697_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45(lean_object* v_msg_2700_, lean_object* v_declHint_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2719_; 
v___x_2709_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg(v_msg_2700_, v_declHint_2701_, v___y_2707_);
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2714_ = l_Lean_unknownIdentifierMessageTag;
v___x_2715_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v_a_2710_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2715_);
v___x_2717_ = v___x_2712_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45___boxed(lean_object* v_msg_2720_, lean_object* v_declHint_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45(v_msg_2720_, v_declHint_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38___redArg(lean_object* v_ref_2730_, lean_object* v_msg_2731_, lean_object* v_declHint_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; lean_object* v_a_2741_; lean_object* v___x_2742_; 
v___x_2740_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45(v_msg_2731_, v_declHint_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2740_);
v___x_2742_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_ref_2730_, v_a_2741_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38___redArg___boxed(lean_object* v_ref_2743_, lean_object* v_msg_2744_, lean_object* v_declHint_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38___redArg(v_ref_2743_, v_msg_2744_, v_declHint_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec(v_ref_2743_);
return v_res_2753_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__1(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__0));
v___x_2756_ = l_Lean_stringToMessageData(v___x_2755_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg(lean_object* v_ref_2757_, lean_object* v_constName_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; uint8_t v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2766_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___closed__1);
v___x_2767_ = 0;
lean_inc(v_constName_2758_);
v___x_2768_ = l_Lean_MessageData_ofConstName(v_constName_2758_, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2766_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38___redArg(v_ref_2757_, v___x_2771_, v_constName_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg___boxed(lean_object* v_ref_2773_, lean_object* v_constName_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg(v_ref_2773_, v_constName_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec(v_ref_2773_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18___redArg(lean_object* v_constName_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_ref_2791_; lean_object* v___x_2792_; 
v_ref_2791_ = lean_ctor_get(v___y_2788_, 5);
lean_inc(v_ref_2791_);
v___x_2792_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg(v_ref_2791_, v_constName_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v_ref_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18___redArg___boxed(lean_object* v_constName_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18___redArg(v_constName_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(lean_object* v_constName_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
lean_object* v___x_2810_; lean_object* v_env_2811_; uint8_t v___x_2812_; lean_object* v___x_2813_; 
v___x_2810_ = lean_st_ref_get(v___y_2808_);
v_env_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc_ref(v_env_2811_);
lean_dec(v___x_2810_);
v___x_2812_ = 0;
lean_inc(v_constName_2802_);
v___x_2813_ = l_Lean_Environment_findConstVal_x3f(v_env_2811_, v_constName_2802_, v___x_2812_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18___redArg(v_constName_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
return v___x_2814_;
}
else
{
lean_object* v_val_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2803_);
lean_dec(v_constName_2802_);
v_val_2815_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2813_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_val_2815_);
lean_dec(v___x_2813_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set_tag(v___x_2817_, 0);
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_val_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3___boxed(lean_object* v_constName_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(v_constName_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(lean_object* v_constName_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___x_2840_; 
lean_inc(v_constName_2832_);
v___x_2840_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(v_constName_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2852_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2852_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2852_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v_levelParams_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v_levelParams_2845_ = lean_ctor_get(v_a_2841_, 1);
lean_inc(v_levelParams_2845_);
lean_dec(v_a_2841_);
v___x_2846_ = lean_box(0);
v___x_2847_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__4(v_levelParams_2845_, v___x_2846_);
v___x_2848_ = l_Lean_mkConst(v_constName_2832_, v___x_2847_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2848_);
v___x_2850_ = v___x_2843_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_constName_2832_);
v_a_2853_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2840_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2840_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1___boxed(lean_object* v_constName_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(v_constName_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
return v_res_2869_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2870_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2873_ = lean_box(1);
v___x_2874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg___closed__4);
v___x_2875_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1);
v___x_2876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
lean_ctor_set(v___x_2876_, 1, v___x_2874_);
lean_ctor_set(v___x_2876_, 2, v___x_2873_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0(uint8_t v___x_2877_, lean_object* v_declName_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_ref_2886_; lean_object* v___x_2887_; 
v_ref_2886_ = lean_ctor_get(v___y_2883_, 5);
lean_inc_ref(v___y_2883_);
lean_inc_ref(v___y_2879_);
v___x_2887_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(v_declName_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref(v___x_2887_);
v___x_2889_ = lean_box(0);
lean_inc(v_ref_2886_);
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v_ref_2886_);
v___x_2891_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2);
v___x_2892_ = lean_box(0);
v___x_2893_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2893_, 0, v___x_2890_);
lean_ctor_set(v___x_2893_, 1, v___x_2891_);
lean_ctor_set(v___x_2893_, 2, v___x_2892_);
lean_ctor_set(v___x_2893_, 3, v_a_2888_);
lean_ctor_set_uint8(v___x_2893_, sizeof(void*)*4, v___x_2877_);
lean_ctor_set_uint8(v___x_2893_, sizeof(void*)*4 + 1, v___x_2877_);
v___x_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
v___x_2895_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(v___x_2894_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec_ref(v___y_2879_);
return v___x_2895_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref(v___y_2883_);
lean_dec_ref(v___y_2879_);
v_a_2896_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2887_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2887_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___boxed(lean_object* v___x_2904_, lean_object* v_declName_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
uint8_t v___x_57500__boxed_2913_; lean_object* v_res_2914_; 
v___x_57500__boxed_2913_ = lean_unbox(v___x_2904_);
v_res_2914_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0(v___x_57500__boxed_2913_, v_declName_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
return v_res_2914_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__0));
v___x_2917_ = l_Lean_stringToMessageData(v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2(lean_object* v_env_2918_, lean_object* v_declName_2919_, lean_object* v___f_2920_, lean_object* v_addInfo_2921_, lean_object* v_____r_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; uint8_t v___x_2931_; uint8_t v___x_2932_; 
lean_inc(v_declName_2919_);
v___x_2930_ = l_Lean_mkPrivateName(v_env_2918_, v_declName_2919_);
v___x_2931_ = 1;
lean_inc(v___x_2930_);
v___x_2932_ = l_Lean_Environment_contains(v_env_2918_, v___x_2930_, v___x_2931_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v___x_2930_);
lean_dec_ref(v_addInfo_2921_);
lean_dec(v_declName_2919_);
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_apply_8(v___f_2920_, v___x_2933_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, lean_box(0));
return v___x_2934_;
}
else
{
lean_object* v___x_2935_; 
lean_dec_ref(v___f_2920_);
lean_inc(v___y_2928_);
lean_inc_ref(v___y_2927_);
lean_inc(v___y_2926_);
lean_inc_ref(v___y_2925_);
lean_inc(v___y_2924_);
lean_inc_ref(v___y_2923_);
v___x_2935_ = lean_apply_8(v_addInfo_2921_, v___x_2930_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, lean_box(0));
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec_ref(v___x_2935_);
v___x_2936_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1);
v___x_2937_ = l_Lean_MessageData_ofConstName(v_declName_2919_, v___x_2931_);
v___x_2938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2940_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
return v___x_2941_;
}
else
{
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v_declName_2919_);
return v___x_2935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___boxed(lean_object* v_env_2942_, lean_object* v_declName_2943_, lean_object* v___f_2944_, lean_object* v_addInfo_2945_, lean_object* v_____r_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2(v_env_2942_, v_declName_2943_, v___f_2944_, v_addInfo_2945_, v_____r_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4(lean_object* v___f_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; lean_object* v_env_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_st_ref_get(v___y_2961_);
v_env_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc_ref(v_env_2964_);
lean_dec(v___x_2963_);
v___x_2965_ = lean_apply_8(v___f_2955_, v_env_2964_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, lean_box(0));
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4___boxed(lean_object* v___f_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4(v___f_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
return v_res_2974_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__0));
v___x_2977_ = l_Lean_stringToMessageData(v___x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1(lean_object* v_declName_2978_, lean_object* v_env_2979_, lean_object* v_addInfo_2980_, lean_object* v_____r_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = lean_private_to_user_name(v_declName_2978_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec_ref(v_addInfo_2980_);
lean_dec_ref(v_env_2979_);
v___x_2990_ = lean_box(0);
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
else
{
lean_object* v_val_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3009_; 
v_val_2992_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2994_ = v___x_2989_;
v_isShared_2995_ = v_isSharedCheck_3009_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_val_2992_);
lean_dec(v___x_2989_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3009_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
uint8_t v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = 1;
lean_inc(v_val_2992_);
v___x_2997_ = l_Lean_Environment_contains(v_env_2979_, v_val_2992_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_3000_; 
lean_dec(v_val_2992_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec_ref(v_addInfo_2980_);
v___x_2998_ = lean_box(0);
if (v_isShared_2995_ == 0)
{
lean_ctor_set_tag(v___x_2994_, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2998_);
v___x_3000_ = v___x_2994_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
else
{
lean_object* v___x_3002_; 
lean_del_object(v___x_2994_);
lean_inc(v___y_2987_);
lean_inc_ref(v___y_2986_);
lean_inc(v___y_2985_);
lean_inc_ref(v___y_2984_);
lean_inc(v___y_2983_);
lean_inc_ref(v___y_2982_);
lean_inc(v_val_2992_);
v___x_3002_ = lean_apply_8(v_addInfo_2980_, v_val_2992_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, lean_box(0));
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec_ref(v___x_3002_);
v___x_3003_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1);
v___x_3004_ = l_Lean_MessageData_ofConstName(v_val_2992_, v___x_2996_);
v___x_3005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_3007_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
return v___x_3008_;
}
else
{
lean_dec(v_val_2992_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
return v___x_3002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___boxed(lean_object* v_declName_3010_, lean_object* v_env_3011_, lean_object* v_addInfo_3012_, lean_object* v_____r_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1(v_declName_3010_, v_env_3011_, v_addInfo_3012_, v_____r_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(lean_object* v_env_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___x_3026_; lean_object* v_nextMacroScope_3027_; lean_object* v_ngen_3028_; lean_object* v_auxDeclNGen_3029_; lean_object* v_traceState_3030_; lean_object* v_messages_3031_; lean_object* v_infoState_3032_; lean_object* v_snapshotTasks_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3059_; 
v___x_3026_ = lean_st_ref_take(v___y_3024_);
v_nextMacroScope_3027_ = lean_ctor_get(v___x_3026_, 1);
v_ngen_3028_ = lean_ctor_get(v___x_3026_, 2);
v_auxDeclNGen_3029_ = lean_ctor_get(v___x_3026_, 3);
v_traceState_3030_ = lean_ctor_get(v___x_3026_, 4);
v_messages_3031_ = lean_ctor_get(v___x_3026_, 6);
v_infoState_3032_ = lean_ctor_get(v___x_3026_, 7);
v_snapshotTasks_3033_ = lean_ctor_get(v___x_3026_, 8);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3059_ == 0)
{
lean_object* v_unused_3060_; lean_object* v_unused_3061_; 
v_unused_3060_ = lean_ctor_get(v___x_3026_, 5);
lean_dec(v_unused_3060_);
v_unused_3061_ = lean_ctor_get(v___x_3026_, 0);
lean_dec(v_unused_3061_);
v___x_3035_ = v___x_3026_;
v_isShared_3036_ = v_isSharedCheck_3059_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_snapshotTasks_3033_);
lean_inc(v_infoState_3032_);
lean_inc(v_messages_3031_);
lean_inc(v_traceState_3030_);
lean_inc(v_auxDeclNGen_3029_);
lean_inc(v_ngen_3028_);
lean_inc(v_nextMacroScope_3027_);
lean_dec(v___x_3026_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3059_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3037_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 5, v___x_3037_);
lean_ctor_set(v___x_3035_, 0, v_env_3022_);
v___x_3039_ = v___x_3035_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_env_3022_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v_nextMacroScope_3027_);
lean_ctor_set(v_reuseFailAlloc_3058_, 2, v_ngen_3028_);
lean_ctor_set(v_reuseFailAlloc_3058_, 3, v_auxDeclNGen_3029_);
lean_ctor_set(v_reuseFailAlloc_3058_, 4, v_traceState_3030_);
lean_ctor_set(v_reuseFailAlloc_3058_, 5, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3058_, 6, v_messages_3031_);
lean_ctor_set(v_reuseFailAlloc_3058_, 7, v_infoState_3032_);
lean_ctor_set(v_reuseFailAlloc_3058_, 8, v_snapshotTasks_3033_);
v___x_3039_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v_mctx_3042_; lean_object* v_zetaDeltaFVarIds_3043_; lean_object* v_postponed_3044_; lean_object* v_diag_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3056_; 
v___x_3040_ = lean_st_ref_set(v___y_3024_, v___x_3039_);
v___x_3041_ = lean_st_ref_take(v___y_3023_);
v_mctx_3042_ = lean_ctor_get(v___x_3041_, 0);
v_zetaDeltaFVarIds_3043_ = lean_ctor_get(v___x_3041_, 2);
v_postponed_3044_ = lean_ctor_get(v___x_3041_, 3);
v_diag_3045_ = lean_ctor_get(v___x_3041_, 4);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v___x_3041_, 1);
lean_dec(v_unused_3057_);
v___x_3047_ = v___x_3041_;
v_isShared_3048_ = v_isSharedCheck_3056_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_diag_3045_);
lean_inc(v_postponed_3044_);
lean_inc(v_zetaDeltaFVarIds_3043_);
lean_inc(v_mctx_3042_);
lean_dec(v___x_3041_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3056_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3049_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 1, v___x_3049_);
v___x_3051_ = v___x_3047_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_mctx_3042_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_zetaDeltaFVarIds_3043_);
lean_ctor_set(v_reuseFailAlloc_3055_, 3, v_postponed_3044_);
lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_diag_3045_);
v___x_3051_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_st_ref_set(v___y_3023_, v___x_3051_);
v___x_3053_ = lean_box(0);
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
return v___x_3054_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_env_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec(v___y_3063_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(lean_object* v_env_3067_, lean_object* v_x_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; lean_object* v_env_3077_; lean_object* v_a_3079_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3076_ = lean_st_ref_get(v___y_3074_);
v_env_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc_ref(v_env_3077_);
lean_dec(v___x_3076_);
v___x_3089_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3067_, v___y_3072_, v___y_3074_);
lean_dec_ref(v___x_3089_);
lean_inc(v___y_3074_);
lean_inc(v___y_3072_);
v___x_3090_ = lean_apply_7(v_x_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, lean_box(0));
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v___x_3090_);
v___x_3092_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3077_, v___y_3072_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec(v___y_3072_);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3092_, 0);
lean_dec(v_unused_3100_);
v___x_3094_ = v___x_3092_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_dec(v___x_3092_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v_a_3091_);
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3091_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_object* v_a_3101_; 
v_a_3101_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3101_);
lean_dec_ref(v___x_3090_);
v_a_3079_ = v_a_3101_;
goto v___jp_3078_;
}
v___jp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
v___x_3080_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3077_, v___y_3072_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec(v___y_3072_);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3080_, 0);
lean_dec(v_unused_3088_);
v___x_3082_ = v___x_3080_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_dec(v___x_3080_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set_tag(v___x_3082_, 1);
lean_ctor_set(v___x_3082_, 0, v_a_3079_);
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3079_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg___boxed(lean_object* v_env_3102_, lean_object* v_x_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3102_, v_x_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(lean_object* v_declName_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v___x_3123_; lean_object* v_env_3124_; uint8_t v___x_3125_; lean_object* v_addInfo_3126_; lean_object* v_env_3127_; lean_object* v___f_3128_; lean_object* v___f_3129_; lean_object* v___x_3130_; lean_object* v___f_3131_; uint8_t v___x_3132_; uint8_t v___x_3133_; 
v___x_3123_ = lean_st_ref_get(v___y_3121_);
v_env_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc_ref(v_env_3124_);
lean_dec(v___x_3123_);
v___x_3125_ = 0;
v_addInfo_3126_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___closed__0));
v_env_3127_ = l_Lean_Environment_setExporting(v_env_3124_, v___x_3125_);
lean_inc_ref(v_env_3127_);
lean_inc(v_declName_3115_);
v___f_3128_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3128_, 0, v_declName_3115_);
lean_closure_set(v___f_3128_, 1, v_env_3127_);
lean_closure_set(v___f_3128_, 2, v_addInfo_3126_);
lean_inc(v_declName_3115_);
lean_inc_ref(v_env_3127_);
v___f_3129_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3129_, 0, v_env_3127_);
lean_closure_set(v___f_3129_, 1, v_declName_3115_);
lean_closure_set(v___f_3129_, 2, v___f_3128_);
lean_closure_set(v___f_3129_, 3, v_addInfo_3126_);
v___x_3130_ = lean_box(v___x_3125_);
lean_inc_ref(v_env_3127_);
lean_inc(v_declName_3115_);
lean_inc_ref(v___f_3129_);
v___f_3131_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___boxed), 12, 4);
lean_closure_set(v___f_3131_, 0, v___f_3129_);
lean_closure_set(v___f_3131_, 1, v_declName_3115_);
lean_closure_set(v___f_3131_, 2, v___x_3130_);
lean_closure_set(v___f_3131_, 3, v_env_3127_);
v___x_3132_ = 1;
lean_inc(v_declName_3115_);
lean_inc_ref(v_env_3127_);
v___x_3133_ = l_Lean_Environment_contains(v_env_3127_, v_declName_3115_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_object* v___f_3134_; lean_object* v___x_3135_; 
lean_dec_ref(v___f_3129_);
lean_dec(v_declName_3115_);
v___f_3134_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4___boxed), 8, 1);
lean_closure_set(v___f_3134_, 0, v___f_3131_);
v___x_3135_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3127_, v___f_3134_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
return v___x_3135_;
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___f_3138_; lean_object* v___x_3139_; 
v___x_3136_ = lean_box(v___x_3132_);
v___x_3137_ = lean_box(v___x_3125_);
lean_inc_ref(v_env_3127_);
v___f_3138_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___boxed), 14, 7);
lean_closure_set(v___f_3138_, 0, v_addInfo_3126_);
lean_closure_set(v___f_3138_, 1, v_declName_3115_);
lean_closure_set(v___f_3138_, 2, v___x_3136_);
lean_closure_set(v___f_3138_, 3, v___f_3129_);
lean_closure_set(v___f_3138_, 4, v___x_3137_);
lean_closure_set(v___f_3138_, 5, v_env_3127_);
lean_closure_set(v___f_3138_, 6, v___f_3131_);
v___x_3139_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3127_, v___f_3138_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
return v___x_3139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___boxed(lean_object* v_declName_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(v_declName_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v_res_3148_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__1));
v___x_3153_ = l_Lean_MessageData_ofFormat(v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0(lean_object* v___x_3154_, uint8_t v___x_3155_, uint8_t v___x_3156_, lean_object* v_xs_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
lean_inc(v___y_3163_);
lean_inc_ref(v___y_3162_);
lean_inc(v___y_3161_);
lean_inc_ref(v___y_3160_);
lean_inc(v___y_3159_);
lean_inc(v___x_3154_);
v___x_3165_ = l_Lean_Elab_Term_elabType(v___x_3154_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref(v___x_3165_);
v___x_3167_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2);
v___x_3168_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_3166_, v___x_3154_, v___x_3167_, v___y_3159_);
lean_dec(v___y_3159_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v___x_3169_; lean_object* v_fst_3170_; lean_object* v_snd_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3196_; 
lean_dec_ref(v___x_3168_);
v___x_3169_ = l_Array_unzip___redArg(v_xs_3157_);
v_fst_3170_ = lean_ctor_get(v___x_3169_, 0);
v_snd_3171_ = lean_ctor_get(v___x_3169_, 1);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3173_ = v___x_3169_;
v_isShared_3174_ = v_isSharedCheck_3196_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_snd_3171_);
lean_inc(v_fst_3170_);
lean_dec(v___x_3169_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3196_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
uint8_t v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = 1;
v___x_3176_ = l_Lean_Meta_mkForallFVars(v_snd_3171_, v_a_3166_, v___x_3155_, v___x_3156_, v___x_3156_, v___x_3175_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v_snd_3171_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3187_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3187_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3187_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 1, v_fst_3170_);
lean_ctor_set(v___x_3173_, 0, v_a_3177_);
v___x_3182_ = v___x_3173_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3177_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v_fst_3170_);
v___x_3182_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3184_; 
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 0, v___x_3182_);
v___x_3184_ = v___x_3179_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_del_object(v___x_3173_);
lean_dec(v_fst_3170_);
v_a_3188_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3176_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3176_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_a_3166_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
v_a_3197_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3168_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3168_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec(v___x_3154_);
v_a_3205_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3165_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3165_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___boxed(lean_object* v___x_3213_, lean_object* v___x_3214_, lean_object* v___x_3215_, lean_object* v_xs_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
uint8_t v___x_57956__boxed_3224_; uint8_t v___x_57957__boxed_3225_; lean_object* v_res_3226_; 
v___x_57956__boxed_3224_ = lean_unbox(v___x_3214_);
v___x_57957__boxed_3225_ = lean_unbox(v___x_3215_);
v_res_3226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0(v___x_3213_, v___x_57956__boxed_3224_, v___x_57957__boxed_3225_, v_xs_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
lean_dec_ref(v_xs_3216_);
return v_res_3226_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(lean_object* v_declName_3227_, lean_object* v_as_3228_, size_t v_i_3229_, size_t v_stop_3230_){
_start:
{
uint8_t v___x_3231_; 
v___x_3231_ = lean_usize_dec_eq(v_i_3229_, v_stop_3230_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v_declName_3233_; uint8_t v___x_3234_; 
v___x_3232_ = lean_array_uget_borrowed(v_as_3228_, v_i_3229_);
v_declName_3233_ = lean_ctor_get(v___x_3232_, 3);
v___x_3234_ = lean_name_eq(v_declName_3233_, v_declName_3227_);
if (v___x_3234_ == 0)
{
size_t v___x_3235_; size_t v___x_3236_; 
v___x_3235_ = ((size_t)1ULL);
v___x_3236_ = lean_usize_add(v_i_3229_, v___x_3235_);
v_i_3229_ = v___x_3236_;
goto _start;
}
else
{
return v___x_3234_;
}
}
else
{
uint8_t v___x_3238_; 
v___x_3238_ = 0;
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6___boxed(lean_object* v_declName_3239_, lean_object* v_as_3240_, lean_object* v_i_3241_, lean_object* v_stop_3242_){
_start:
{
size_t v_i_boxed_3243_; size_t v_stop_boxed_3244_; uint8_t v_res_3245_; lean_object* v_r_3246_; 
v_i_boxed_3243_ = lean_unbox_usize(v_i_3241_);
lean_dec(v_i_3241_);
v_stop_boxed_3244_ = lean_unbox_usize(v_stop_3242_);
lean_dec(v_stop_3242_);
v_res_3245_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(v_declName_3239_, v_as_3240_, v_i_boxed_3243_, v_stop_boxed_3244_);
lean_dec_ref(v_as_3240_);
lean_dec(v_declName_3239_);
v_r_3246_ = lean_box(v_res_3245_);
return v_r_3246_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__0));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9(void){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__8));
v___x_3270_ = l_Lean_stringToMessageData(v___x_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(uint8_t v___x_3271_, lean_object* v_as_3272_, size_t v_sz_3273_, size_t v_i_3274_, lean_object* v_b_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_a_3284_; uint8_t v___x_3288_; 
v___x_3288_ = lean_usize_dec_lt(v_i_3274_, v_sz_3273_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
v___x_3289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3289_, 0, v_b_3275_);
return v___x_3289_;
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v_a_3292_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v_valStx_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; uint8_t v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; uint8_t v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; uint8_t v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; uint8_t v___y_3437_; uint8_t v___y_3471_; uint8_t v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v_declName_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; uint8_t v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; uint8_t v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; uint8_t v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; uint8_t v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; uint8_t v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; uint8_t v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; uint8_t v___y_3538_; uint8_t v___y_3539_; lean_object* v___y_3540_; uint8_t v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3566_; uint8_t v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; uint8_t v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3593_; lean_object* v_attrs_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3630_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3290_ = lean_unsigned_to_nat(0u);
v___x_3291_ = lean_unsigned_to_nat(1u);
v_a_3292_ = lean_array_uget_borrowed(v_as_3272_, v_i_3274_);
v___x_3645_ = l_Lean_Syntax_getArg(v_a_3292_, v___x_3290_);
v___x_3646_ = l_Lean_Syntax_getOptional_x3f(v___x_3645_);
lean_dec(v___x_3645_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_box(0);
v___y_3630_ = v___x_3647_;
goto v___jp_3629_;
}
else
{
lean_object* v_val_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3657_; 
v_val_3648_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3650_ = v___x_3646_;
v_isShared_3651_ = v_isSharedCheck_3657_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_val_3648_);
lean_dec(v___x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3657_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3652_ = lean_box(v___x_3271_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v_val_3648_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3653_);
v___x_3655_ = v___x_3650_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
v___y_3630_ = v___x_3655_;
goto v___jp_3629_;
}
}
}
v___jp_3293_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = lean_unsigned_to_nat(3u);
v___x_3312_ = l_Lean_Syntax_getArg(v_a_3292_, v___x_3311_);
v___x_3313_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(v___x_3312_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref(v___x_3313_);
v___x_3315_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3315_, 0, v___y_3302_);
lean_ctor_set(v___x_3315_, 1, v___y_3301_);
lean_ctor_set(v___x_3315_, 2, v___y_3295_);
lean_ctor_set(v___x_3315_, 3, v___y_3300_);
lean_ctor_set(v___x_3315_, 4, v___y_3297_);
lean_ctor_set(v___x_3315_, 5, v___y_3294_);
lean_ctor_set(v___x_3315_, 6, v___y_3296_);
lean_ctor_set(v___x_3315_, 7, v___y_3299_);
lean_ctor_set(v___x_3315_, 8, v___y_3298_);
lean_ctor_set(v___x_3315_, 9, v_valStx_3304_);
lean_ctor_set(v___x_3315_, 10, v_a_3314_);
lean_ctor_set(v___x_3315_, 11, v___y_3303_);
v___x_3316_ = lean_array_push(v_b_3275_, v___x_3315_);
v_a_3284_ = v___x_3316_;
goto v___jp_3283_;
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_valStx_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3317_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3313_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3313_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
v___jp_3325_:
{
lean_object* v___x_3342_; 
lean_inc(v___y_3341_);
lean_inc_ref(v___y_3340_);
lean_inc(v___y_3339_);
lean_inc_ref(v___y_3338_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc(v___y_3331_);
v___x_3342_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(v___y_3331_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3342_) == 0)
{
uint8_t v___x_3343_; lean_object* v___x_3344_; 
lean_dec_ref(v___x_3342_);
v___x_3343_ = 2;
lean_inc(v___y_3341_);
lean_inc_ref(v___y_3340_);
lean_inc(v___y_3339_);
lean_inc_ref(v___y_3338_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc_ref(v___y_3333_);
lean_inc(v___y_3331_);
v___x_3344_ = l_Lean_Elab_Term_applyAttributesAt(v___y_3331_, v___y_3333_, v___x_3343_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3345_; 
lean_dec_ref(v___x_3344_);
lean_inc_ref(v___y_3340_);
lean_inc(v___y_3331_);
v___x_3345_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(v___y_3331_, v___y_3329_, v___y_3332_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___f_3352_; lean_object* v___x_3353_; 
lean_dec_ref(v___x_3345_);
v___x_3346_ = l_Lean_Syntax_getArg(v___y_3329_, v___x_3291_);
v___x_3347_ = l_Lean_Syntax_getArgs(v___x_3346_);
v___x_3348_ = l_Lean_Syntax_getArg(v___y_3329_, v___y_3334_);
v___x_3349_ = l_Lean_Elab_Term_expandOptType(v___y_3332_, v___x_3348_);
lean_dec(v___x_3348_);
v___x_3350_ = lean_box(v___y_3326_);
v___x_3351_ = lean_box(v___x_3288_);
v___f_3352_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3352_, 0, v___x_3349_);
lean_closure_set(v___f_3352_, 1, v___x_3350_);
lean_closure_set(v___f_3352_, 2, v___x_3351_);
lean_inc(v___y_3341_);
lean_inc_ref(v___y_3340_);
lean_inc(v___y_3339_);
lean_inc_ref(v___y_3338_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
v___x_3353_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___x_3347_, v___f_3352_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v_fst_3355_; lean_object* v_snd_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref(v___x_3353_);
v_fst_3355_ = lean_ctor_get(v_a_3354_, 0);
lean_inc(v_fst_3355_);
v_snd_3356_ = lean_ctor_get(v_a_3354_, 1);
lean_inc(v_snd_3356_);
lean_dec(v_a_3354_);
lean_inc(v_fst_3355_);
v___x_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_fst_3355_);
v___x_3358_ = 2;
v___x_3359_ = lean_box(0);
lean_inc_ref(v___y_3338_);
v___x_3360_ = l_Lean_Meta_mkFreshExprMVar(v___x_3357_, v___x_3358_, v___x_3359_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3360_) == 0)
{
if (v___y_3330_ == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref(v___x_3360_);
v___x_3362_ = lean_unsigned_to_nat(3u);
v___x_3363_ = l_Lean_Syntax_getArg(v___y_3329_, v___x_3362_);
v___x_3364_ = lean_box(v___x_3288_);
v___x_3365_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed), 5, 3);
lean_closure_set(v___x_3365_, 0, v___y_3329_);
lean_closure_set(v___x_3365_, 1, v___x_3363_);
lean_closure_set(v___x_3365_, 2, v___x_3364_);
lean_inc_ref(v___y_3340_);
lean_inc_ref(v___y_3336_);
v___x_3366_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_3365_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref(v___x_3366_);
v___y_3294_ = v_snd_3356_;
v___y_3295_ = v___y_3327_;
v___y_3296_ = v___x_3346_;
v___y_3297_ = v___y_3328_;
v___y_3298_ = v_a_3361_;
v___y_3299_ = v_fst_3355_;
v___y_3300_ = v___y_3331_;
v___y_3301_ = v___y_3333_;
v___y_3302_ = v___y_3332_;
v___y_3303_ = v___y_3335_;
v_valStx_3304_ = v_a_3367_;
v___y_3305_ = v___y_3336_;
v___y_3306_ = v___y_3337_;
v___y_3307_ = v___y_3338_;
v___y_3308_ = v___y_3339_;
v___y_3309_ = v___y_3340_;
v___y_3310_ = v___y_3341_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec(v_a_3361_);
lean_dec(v_snd_3356_);
lean_dec(v_fst_3355_);
lean_dec(v___x_3346_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3368_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3366_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_a_3376_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3376_);
lean_dec_ref(v___x_3360_);
v___x_3377_ = lean_unsigned_to_nat(4u);
v___x_3378_ = l_Lean_Syntax_getArg(v___y_3329_, v___x_3377_);
lean_dec(v___y_3329_);
v___y_3294_ = v_snd_3356_;
v___y_3295_ = v___y_3327_;
v___y_3296_ = v___x_3346_;
v___y_3297_ = v___y_3328_;
v___y_3298_ = v_a_3376_;
v___y_3299_ = v_fst_3355_;
v___y_3300_ = v___y_3331_;
v___y_3301_ = v___y_3333_;
v___y_3302_ = v___y_3332_;
v___y_3303_ = v___y_3335_;
v_valStx_3304_ = v___x_3378_;
v___y_3305_ = v___y_3336_;
v___y_3306_ = v___y_3337_;
v___y_3307_ = v___y_3338_;
v___y_3308_ = v___y_3339_;
v___y_3309_ = v___y_3340_;
v___y_3310_ = v___y_3341_;
goto v___jp_3293_;
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v_snd_3356_);
lean_dec(v_fst_3355_);
lean_dec(v___x_3346_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3379_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3360_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3360_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v___x_3346_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3387_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3353_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3353_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3395_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3345_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3345_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3403_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3344_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3344_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3411_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3342_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3342_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
v___jp_3419_:
{
if (v___y_3437_ == 0)
{
v___y_3326_ = v___y_3420_;
v___y_3327_ = v___y_3421_;
v___y_3328_ = v___y_3431_;
v___y_3329_ = v___y_3432_;
v___y_3330_ = v___y_3423_;
v___y_3331_ = v___y_3434_;
v___y_3332_ = v___y_3426_;
v___y_3333_ = v___y_3424_;
v___y_3334_ = v___y_3427_;
v___y_3335_ = v___y_3429_;
v___y_3336_ = v___y_3436_;
v___y_3337_ = v___y_3435_;
v___y_3338_ = v___y_3433_;
v___y_3339_ = v___y_3428_;
v___y_3340_ = v___y_3425_;
v___y_3341_ = v___y_3422_;
goto v___jp_3325_;
}
else
{
lean_object* v_fileName_3438_; lean_object* v_fileMap_3439_; lean_object* v_options_3440_; lean_object* v_currRecDepth_3441_; lean_object* v_maxRecDepth_3442_; lean_object* v_ref_3443_; lean_object* v_currNamespace_3444_; lean_object* v_openDecls_3445_; lean_object* v_initHeartbeats_3446_; lean_object* v_maxHeartbeats_3447_; lean_object* v_quotContext_3448_; lean_object* v_currMacroScope_3449_; uint8_t v_diag_3450_; lean_object* v_cancelTk_x3f_3451_; uint8_t v_suppressElabErrors_3452_; lean_object* v_inheritedTraceOptions_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v_ref_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v_fileName_3438_ = lean_ctor_get(v___y_3425_, 0);
v_fileMap_3439_ = lean_ctor_get(v___y_3425_, 1);
v_options_3440_ = lean_ctor_get(v___y_3425_, 2);
v_currRecDepth_3441_ = lean_ctor_get(v___y_3425_, 3);
v_maxRecDepth_3442_ = lean_ctor_get(v___y_3425_, 4);
v_ref_3443_ = lean_ctor_get(v___y_3425_, 5);
v_currNamespace_3444_ = lean_ctor_get(v___y_3425_, 6);
v_openDecls_3445_ = lean_ctor_get(v___y_3425_, 7);
v_initHeartbeats_3446_ = lean_ctor_get(v___y_3425_, 8);
v_maxHeartbeats_3447_ = lean_ctor_get(v___y_3425_, 9);
v_quotContext_3448_ = lean_ctor_get(v___y_3425_, 10);
v_currMacroScope_3449_ = lean_ctor_get(v___y_3425_, 11);
v_diag_3450_ = lean_ctor_get_uint8(v___y_3425_, sizeof(void*)*14);
v_cancelTk_x3f_3451_ = lean_ctor_get(v___y_3425_, 12);
v_suppressElabErrors_3452_ = lean_ctor_get_uint8(v___y_3425_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3453_ = lean_ctor_get(v___y_3425_, 13);
v___x_3454_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
lean_inc(v___y_3434_);
v___x_3455_ = l_Lean_MessageData_ofConstName(v___y_3434_, v___y_3430_);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v_ref_3459_ = l_Lean_replaceRef(v___y_3426_, v_ref_3443_);
lean_inc_ref(v_inheritedTraceOptions_3453_);
lean_inc(v_cancelTk_x3f_3451_);
lean_inc(v_currMacroScope_3449_);
lean_inc(v_quotContext_3448_);
lean_inc(v_maxHeartbeats_3447_);
lean_inc(v_initHeartbeats_3446_);
lean_inc(v_openDecls_3445_);
lean_inc(v_currNamespace_3444_);
lean_inc(v_maxRecDepth_3442_);
lean_inc(v_currRecDepth_3441_);
lean_inc_ref(v_options_3440_);
lean_inc_ref(v_fileMap_3439_);
lean_inc_ref(v_fileName_3438_);
v___x_3460_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3460_, 0, v_fileName_3438_);
lean_ctor_set(v___x_3460_, 1, v_fileMap_3439_);
lean_ctor_set(v___x_3460_, 2, v_options_3440_);
lean_ctor_set(v___x_3460_, 3, v_currRecDepth_3441_);
lean_ctor_set(v___x_3460_, 4, v_maxRecDepth_3442_);
lean_ctor_set(v___x_3460_, 5, v_ref_3459_);
lean_ctor_set(v___x_3460_, 6, v_currNamespace_3444_);
lean_ctor_set(v___x_3460_, 7, v_openDecls_3445_);
lean_ctor_set(v___x_3460_, 8, v_initHeartbeats_3446_);
lean_ctor_set(v___x_3460_, 9, v_maxHeartbeats_3447_);
lean_ctor_set(v___x_3460_, 10, v_quotContext_3448_);
lean_ctor_set(v___x_3460_, 11, v_currMacroScope_3449_);
lean_ctor_set(v___x_3460_, 12, v_cancelTk_x3f_3451_);
lean_ctor_set(v___x_3460_, 13, v_inheritedTraceOptions_3453_);
lean_ctor_set_uint8(v___x_3460_, sizeof(void*)*14, v_diag_3450_);
lean_ctor_set_uint8(v___x_3460_, sizeof(void*)*14 + 1, v_suppressElabErrors_3452_);
lean_inc_ref(v___y_3436_);
v___x_3461_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_3458_, v___y_3436_, v___y_3435_, v___y_3433_, v___y_3428_, v___x_3460_, v___y_3422_);
lean_dec_ref(v___x_3460_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_dec_ref(v___x_3461_);
v___y_3326_ = v___y_3420_;
v___y_3327_ = v___y_3421_;
v___y_3328_ = v___y_3431_;
v___y_3329_ = v___y_3432_;
v___y_3330_ = v___y_3423_;
v___y_3331_ = v___y_3434_;
v___y_3332_ = v___y_3426_;
v___y_3333_ = v___y_3424_;
v___y_3334_ = v___y_3427_;
v___y_3335_ = v___y_3429_;
v___y_3336_ = v___y_3436_;
v___y_3337_ = v___y_3435_;
v___y_3338_ = v___y_3433_;
v___y_3339_ = v___y_3428_;
v___y_3340_ = v___y_3425_;
v___y_3341_ = v___y_3422_;
goto v___jp_3325_;
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
v___jp_3470_:
{
lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3488_ = lean_array_get_size(v_b_3275_);
v___x_3489_ = lean_nat_dec_lt(v___x_3290_, v___x_3488_);
if (v___x_3489_ == 0)
{
v___y_3420_ = v___y_3471_;
v___y_3421_ = v___y_3473_;
v___y_3422_ = v___y_3487_;
v___y_3423_ = v___y_3476_;
v___y_3424_ = v___y_3477_;
v___y_3425_ = v___y_3486_;
v___y_3426_ = v___y_3478_;
v___y_3427_ = v___y_3479_;
v___y_3428_ = v___y_3485_;
v___y_3429_ = v___y_3480_;
v___y_3430_ = v___y_3472_;
v___y_3431_ = v___y_3475_;
v___y_3432_ = v___y_3474_;
v___y_3433_ = v___y_3484_;
v___y_3434_ = v_declName_3481_;
v___y_3435_ = v___y_3483_;
v___y_3436_ = v___y_3482_;
v___y_3437_ = v___y_3472_;
goto v___jp_3419_;
}
else
{
if (v___x_3489_ == 0)
{
v___y_3420_ = v___y_3471_;
v___y_3421_ = v___y_3473_;
v___y_3422_ = v___y_3487_;
v___y_3423_ = v___y_3476_;
v___y_3424_ = v___y_3477_;
v___y_3425_ = v___y_3486_;
v___y_3426_ = v___y_3478_;
v___y_3427_ = v___y_3479_;
v___y_3428_ = v___y_3485_;
v___y_3429_ = v___y_3480_;
v___y_3430_ = v___y_3472_;
v___y_3431_ = v___y_3475_;
v___y_3432_ = v___y_3474_;
v___y_3433_ = v___y_3484_;
v___y_3434_ = v_declName_3481_;
v___y_3435_ = v___y_3483_;
v___y_3436_ = v___y_3482_;
v___y_3437_ = v___y_3472_;
goto v___jp_3419_;
}
else
{
size_t v___x_3490_; size_t v___x_3491_; uint8_t v___x_3492_; 
v___x_3490_ = ((size_t)0ULL);
v___x_3491_ = lean_usize_of_nat(v___x_3488_);
v___x_3492_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(v_declName_3481_, v_b_3275_, v___x_3490_, v___x_3491_);
v___y_3420_ = v___y_3471_;
v___y_3421_ = v___y_3473_;
v___y_3422_ = v___y_3487_;
v___y_3423_ = v___y_3476_;
v___y_3424_ = v___y_3477_;
v___y_3425_ = v___y_3486_;
v___y_3426_ = v___y_3478_;
v___y_3427_ = v___y_3479_;
v___y_3428_ = v___y_3485_;
v___y_3429_ = v___y_3480_;
v___y_3430_ = v___y_3472_;
v___y_3431_ = v___y_3475_;
v___y_3432_ = v___y_3474_;
v___y_3433_ = v___y_3484_;
v___y_3434_ = v_declName_3481_;
v___y_3435_ = v___y_3483_;
v___y_3436_ = v___y_3482_;
v___y_3437_ = v___x_3492_;
goto v___jp_3419_;
}
}
}
v___jp_3493_:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_Lean_mkPrivateName(v___y_3505_, v___y_3497_);
lean_dec_ref(v___y_3505_);
v___y_3471_ = v___y_3494_;
v___y_3472_ = v___y_3506_;
v___y_3473_ = v___y_3496_;
v___y_3474_ = v___y_3508_;
v___y_3475_ = v___y_3509_;
v___y_3476_ = v___y_3498_;
v___y_3477_ = v___y_3502_;
v___y_3478_ = v___y_3501_;
v___y_3479_ = v___y_3503_;
v___y_3480_ = v___y_3504_;
v_declName_3481_ = v___x_3512_;
v___y_3482_ = v___y_3500_;
v___y_3483_ = v___y_3507_;
v___y_3484_ = v___y_3511_;
v___y_3485_ = v___y_3510_;
v___y_3486_ = v___y_3499_;
v___y_3487_ = v___y_3495_;
goto v___jp_3470_;
}
v___jp_3513_:
{
lean_object* v___x_3531_; lean_object* v_env_3532_; lean_object* v___x_3533_; uint8_t v_isModule_3534_; lean_object* v___x_3535_; 
v___x_3531_ = lean_st_ref_get(v___y_3516_);
v_env_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc_ref(v_env_3532_);
lean_dec(v___x_3531_);
v___x_3533_ = l_Lean_Environment_header(v_env_3532_);
v_isModule_3534_ = lean_ctor_get_uint8(v___x_3533_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3533_);
lean_inc(v___y_3515_);
v___x_3535_ = l_Lean_Name_append(v___y_3530_, v___y_3515_);
if (v_isModule_3534_ == 0)
{
lean_dec_ref(v_env_3532_);
v___y_3471_ = v___y_3514_;
v___y_3472_ = v___y_3524_;
v___y_3473_ = v___y_3515_;
v___y_3474_ = v___y_3526_;
v___y_3475_ = v___y_3527_;
v___y_3476_ = v___y_3517_;
v___y_3477_ = v___y_3520_;
v___y_3478_ = v___y_3521_;
v___y_3479_ = v___y_3522_;
v___y_3480_ = v___y_3523_;
v_declName_3481_ = v___x_3535_;
v___y_3482_ = v___y_3519_;
v___y_3483_ = v___y_3525_;
v___y_3484_ = v___y_3529_;
v___y_3485_ = v___y_3528_;
v___y_3486_ = v___y_3518_;
v___y_3487_ = v___y_3516_;
goto v___jp_3470_;
}
else
{
uint8_t v_isExporting_3536_; 
v_isExporting_3536_ = lean_ctor_get_uint8(v_env_3532_, sizeof(void*)*8);
if (v_isExporting_3536_ == 0)
{
v___y_3494_ = v___y_3514_;
v___y_3495_ = v___y_3516_;
v___y_3496_ = v___y_3515_;
v___y_3497_ = v___x_3535_;
v___y_3498_ = v___y_3517_;
v___y_3499_ = v___y_3518_;
v___y_3500_ = v___y_3519_;
v___y_3501_ = v___y_3521_;
v___y_3502_ = v___y_3520_;
v___y_3503_ = v___y_3522_;
v___y_3504_ = v___y_3523_;
v___y_3505_ = v_env_3532_;
v___y_3506_ = v___y_3524_;
v___y_3507_ = v___y_3525_;
v___y_3508_ = v___y_3526_;
v___y_3509_ = v___y_3527_;
v___y_3510_ = v___y_3528_;
v___y_3511_ = v___y_3529_;
goto v___jp_3493_;
}
else
{
if (v___y_3524_ == 0)
{
lean_dec_ref(v_env_3532_);
v___y_3471_ = v___y_3514_;
v___y_3472_ = v___y_3524_;
v___y_3473_ = v___y_3515_;
v___y_3474_ = v___y_3526_;
v___y_3475_ = v___y_3527_;
v___y_3476_ = v___y_3517_;
v___y_3477_ = v___y_3520_;
v___y_3478_ = v___y_3521_;
v___y_3479_ = v___y_3522_;
v___y_3480_ = v___y_3523_;
v_declName_3481_ = v___x_3535_;
v___y_3482_ = v___y_3519_;
v___y_3483_ = v___y_3525_;
v___y_3484_ = v___y_3529_;
v___y_3485_ = v___y_3528_;
v___y_3486_ = v___y_3518_;
v___y_3487_ = v___y_3516_;
goto v___jp_3470_;
}
else
{
v___y_3494_ = v___y_3514_;
v___y_3495_ = v___y_3516_;
v___y_3496_ = v___y_3515_;
v___y_3497_ = v___x_3535_;
v___y_3498_ = v___y_3517_;
v___y_3499_ = v___y_3518_;
v___y_3500_ = v___y_3519_;
v___y_3501_ = v___y_3521_;
v___y_3502_ = v___y_3520_;
v___y_3503_ = v___y_3522_;
v___y_3504_ = v___y_3523_;
v___y_3505_ = v_env_3532_;
v___y_3506_ = v___y_3524_;
v___y_3507_ = v___y_3525_;
v___y_3508_ = v___y_3526_;
v___y_3509_ = v___y_3527_;
v___y_3510_ = v___y_3528_;
v___y_3511_ = v___y_3529_;
goto v___jp_3493_;
}
}
}
}
v___jp_3537_:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v___y_3546_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = l_Lean_Syntax_getId(v___y_3543_);
if (lean_obj_tag(v_a_3553_) == 0)
{
lean_object* v___x_3555_; 
v___x_3555_ = lean_box(0);
v___y_3514_ = v___y_3538_;
v___y_3515_ = v___x_3554_;
v___y_3516_ = v___y_3551_;
v___y_3517_ = v___y_3541_;
v___y_3518_ = v___y_3550_;
v___y_3519_ = v___y_3546_;
v___y_3520_ = v___y_3542_;
v___y_3521_ = v___y_3543_;
v___y_3522_ = v___y_3544_;
v___y_3523_ = v___y_3545_;
v___y_3524_ = v___y_3539_;
v___y_3525_ = v___y_3547_;
v___y_3526_ = v___y_3540_;
v___y_3527_ = v_a_3553_;
v___y_3528_ = v___y_3549_;
v___y_3529_ = v___y_3548_;
v___y_3530_ = v___x_3555_;
goto v___jp_3513_;
}
else
{
lean_object* v_val_3556_; 
v_val_3556_ = lean_ctor_get(v_a_3553_, 0);
lean_inc(v_val_3556_);
v___y_3514_ = v___y_3538_;
v___y_3515_ = v___x_3554_;
v___y_3516_ = v___y_3551_;
v___y_3517_ = v___y_3541_;
v___y_3518_ = v___y_3550_;
v___y_3519_ = v___y_3546_;
v___y_3520_ = v___y_3542_;
v___y_3521_ = v___y_3543_;
v___y_3522_ = v___y_3544_;
v___y_3523_ = v___y_3545_;
v___y_3524_ = v___y_3539_;
v___y_3525_ = v___y_3547_;
v___y_3526_ = v___y_3540_;
v___y_3527_ = v_a_3553_;
v___y_3528_ = v___y_3549_;
v___y_3529_ = v___y_3548_;
v___y_3530_ = v_val_3556_;
goto v___jp_3513_;
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec(v___y_3545_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3540_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3557_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3552_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3552_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
v___jp_3565_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3579_ = l_Lean_Syntax_getArg(v___y_3578_, v___x_3290_);
v___x_3580_ = l_Lean_Syntax_getArg(v___x_3579_, v___x_3290_);
lean_dec(v___x_3579_);
v___x_3581_ = l_Lean_Syntax_isIdent(v___x_3580_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1);
lean_inc_ref(v___y_3569_);
lean_inc_ref(v___y_3568_);
v___x_3583_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___x_3580_, v___x_3582_, v___y_3568_, v___y_3570_, v___y_3576_, v___y_3577_, v___y_3569_, v___y_3575_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_dec_ref(v___x_3583_);
v___y_3538_ = v___y_3566_;
v___y_3539_ = v___y_3574_;
v___y_3540_ = v___y_3578_;
v___y_3541_ = v___y_3567_;
v___y_3542_ = v___y_3571_;
v___y_3543_ = v___x_3580_;
v___y_3544_ = v___y_3572_;
v___y_3545_ = v___y_3573_;
v___y_3546_ = v___y_3568_;
v___y_3547_ = v___y_3570_;
v___y_3548_ = v___y_3576_;
v___y_3549_ = v___y_3577_;
v___y_3550_ = v___y_3569_;
v___y_3551_ = v___y_3575_;
goto v___jp_3537_;
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v___x_3580_);
lean_dec(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3583_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
v___y_3538_ = v___y_3566_;
v___y_3539_ = v___y_3574_;
v___y_3540_ = v___y_3578_;
v___y_3541_ = v___y_3567_;
v___y_3542_ = v___y_3571_;
v___y_3543_ = v___x_3580_;
v___y_3544_ = v___y_3572_;
v___y_3545_ = v___y_3573_;
v___y_3546_ = v___y_3568_;
v___y_3547_ = v___y_3570_;
v___y_3548_ = v___y_3576_;
v___y_3549_ = v___y_3577_;
v___y_3550_ = v___y_3569_;
v___y_3551_ = v___y_3575_;
goto v___jp_3537_;
}
}
v___jp_3592_:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3601_ = lean_unsigned_to_nat(2u);
v___x_3602_ = l_Lean_Syntax_getArg(v_a_3292_, v___x_3601_);
v___x_3603_ = l_Lean_Syntax_getArg(v___x_3602_, v___x_3290_);
lean_dec(v___x_3602_);
v___x_3604_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3));
lean_inc(v___x_3603_);
v___x_3605_ = l_Lean_Syntax_isOfKind(v___x_3603_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5));
lean_inc(v___x_3603_);
v___x_3607_ = l_Lean_Syntax_isOfKind(v___x_3603_, v___x_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; uint8_t v___x_3609_; 
v___x_3608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7));
lean_inc(v___x_3603_);
v___x_3609_ = l_Lean_Syntax_isOfKind(v___x_3603_, v___x_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_dec(v___x_3603_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec_ref(v_attrs_3594_);
lean_dec(v___y_3593_);
v___x_3610_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_dec_ref(v___x_3610_);
v_a_3284_ = v_b_3275_;
goto v___jp_3283_;
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
v___y_3566_ = v___x_3605_;
v___y_3567_ = v___x_3607_;
v___y_3568_ = v___y_3595_;
v___y_3569_ = v___y_3599_;
v___y_3570_ = v___y_3596_;
v___y_3571_ = v_attrs_3594_;
v___y_3572_ = v___x_3601_;
v___y_3573_ = v___y_3593_;
v___y_3574_ = v___x_3605_;
v___y_3575_ = v___y_3600_;
v___y_3576_ = v___y_3597_;
v___y_3577_ = v___y_3598_;
v___y_3578_ = v___x_3603_;
goto v___jp_3565_;
}
}
else
{
v___y_3566_ = v___x_3605_;
v___y_3567_ = v___x_3607_;
v___y_3568_ = v___y_3595_;
v___y_3569_ = v___y_3599_;
v___y_3570_ = v___y_3596_;
v___y_3571_ = v_attrs_3594_;
v___y_3572_ = v___x_3601_;
v___y_3573_ = v___y_3593_;
v___y_3574_ = v___x_3605_;
v___y_3575_ = v___y_3600_;
v___y_3576_ = v___y_3597_;
v___y_3577_ = v___y_3598_;
v___y_3578_ = v___x_3603_;
goto v___jp_3565_;
}
}
else
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
lean_dec_ref(v_attrs_3594_);
lean_dec(v___y_3593_);
v___x_3619_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9);
v___x_3620_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___x_3603_, v___x_3619_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec(v___x_3603_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_dec_ref(v___x_3620_);
v_a_3284_ = v_b_3275_;
goto v___jp_3283_;
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3620_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
v___jp_3629_:
{
lean_object* v___x_3631_; uint8_t v___x_3632_; 
v___x_3631_ = l_Lean_Syntax_getArg(v_a_3292_, v___x_3291_);
v___x_3632_ = l_Lean_Syntax_isNone(v___x_3631_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = l_Lean_Syntax_getArg(v___x_3631_, v___x_3290_);
lean_dec(v___x_3631_);
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3280_);
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
lean_inc(v___y_3277_);
lean_inc_ref(v___y_3276_);
v___x_3634_ = l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(v___x_3633_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___x_3633_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref(v___x_3634_);
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3280_);
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
lean_inc(v___y_3277_);
lean_inc_ref(v___y_3276_);
v___y_3593_ = v___y_3630_;
v_attrs_3594_ = v_a_3635_;
v___y_3595_ = v___y_3276_;
v___y_3596_ = v___y_3277_;
v___y_3597_ = v___y_3278_;
v___y_3598_ = v___y_3279_;
v___y_3599_ = v___y_3280_;
v___y_3600_ = v___y_3281_;
goto v___jp_3592_;
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec(v___y_3630_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_b_3275_);
v_a_3636_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3634_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3634_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
else
{
lean_object* v___x_3644_; 
lean_dec(v___x_3631_);
v___x_3644_ = ((lean_object*)(l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23___closed__0));
lean_inc(v___y_3281_);
lean_inc_ref(v___y_3280_);
lean_inc(v___y_3279_);
lean_inc_ref(v___y_3278_);
lean_inc(v___y_3277_);
lean_inc_ref(v___y_3276_);
v___y_3593_ = v___y_3630_;
v_attrs_3594_ = v___x_3644_;
v___y_3595_ = v___y_3276_;
v___y_3596_ = v___y_3277_;
v___y_3597_ = v___y_3278_;
v___y_3598_ = v___y_3279_;
v___y_3599_ = v___y_3280_;
v___y_3600_ = v___y_3281_;
goto v___jp_3592_;
}
}
}
v___jp_3283_:
{
size_t v___x_3285_; size_t v___x_3286_; 
v___x_3285_ = ((size_t)1ULL);
v___x_3286_ = lean_usize_add(v_i_3274_, v___x_3285_);
v_i_3274_ = v___x_3286_;
v_b_3275_ = v_a_3284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___boxed(lean_object* v___x_3658_, lean_object* v_as_3659_, lean_object* v_sz_3660_, lean_object* v_i_3661_, lean_object* v_b_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v___x_58167__boxed_3670_; size_t v_sz_boxed_3671_; size_t v_i_boxed_3672_; lean_object* v_res_3673_; 
v___x_58167__boxed_3670_ = lean_unbox(v___x_3658_);
v_sz_boxed_3671_ = lean_unbox_usize(v_sz_3660_);
lean_dec(v_sz_3660_);
v_i_boxed_3672_ = lean_unbox_usize(v_i_3661_);
lean_dec(v_i_3661_);
v_res_3673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(v___x_58167__boxed_3670_, v_as_3659_, v_sz_boxed_3671_, v_i_boxed_3672_, v_b_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec_ref(v_as_3659_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(lean_object* v_letRec_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v_options_3684_; lean_object* v___x_3685_; lean_object* v_decls_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; size_t v_sz_3693_; size_t v___x_3694_; lean_object* v___x_3695_; 
v_options_3684_ = lean_ctor_get(v_a_3681_, 2);
v___x_3685_ = lean_unsigned_to_nat(0u);
v_decls_3686_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___closed__0));
v___x_3687_ = l_Lean_doc_verso;
v___x_3688_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_options_3684_, v___x_3687_);
v___x_3689_ = lean_unsigned_to_nat(1u);
v___x_3690_ = l_Lean_Syntax_getArg(v_letRec_3676_, v___x_3689_);
v___x_3691_ = l_Lean_Syntax_getArg(v___x_3690_, v___x_3685_);
lean_dec(v___x_3690_);
v___x_3692_ = l_Lean_Syntax_getSepArgs(v___x_3691_);
lean_dec(v___x_3691_);
v_sz_3693_ = lean_array_size(v___x_3692_);
v___x_3694_ = ((size_t)0ULL);
v___x_3695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(v___x_3688_, v___x_3692_, v_sz_3693_, v___x_3694_, v_decls_3686_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_);
lean_dec_ref(v___x_3692_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3706_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3706_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3706_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3700_ = lean_unsigned_to_nat(3u);
v___x_3701_ = l_Lean_Syntax_getArg(v_letRec_3676_, v___x_3700_);
v___x_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3702_, 0, v_a_3696_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3702_);
v___x_3704_ = v___x_3698_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
v_a_3707_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3695_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3695_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___boxed(lean_object* v_letRec_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(v_letRec_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
lean_dec(v_letRec_3715_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5(lean_object* v_stx_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_stx_3724_, v___y_3729_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___boxed(lean_object* v_stx_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5(v_stx_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v_stx_3733_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6(lean_object* v_declName_3742_, lean_object* v_declRanges_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_3742_, v_declRanges_3743_, v___y_3747_, v___y_3749_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___boxed(lean_object* v_declName_3752_, lean_object* v_declRanges_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6(v_declName_3752_, v_declRanges_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(lean_object* v_cls_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_3762_, v___y_3767_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___boxed(lean_object* v_cls_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(v_cls_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(lean_object* v_00_u03b1_3780_, lean_object* v_x_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3784_; 
v___x_3784_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___redArg(v_x_3781_, v___y_3783_);
return v___x_3784_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3785_, lean_object* v_x_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v_00_u03b1_3785_, v_x_3786_, v___y_3787_, v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec_ref(v_x_3786_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15(lean_object* v_00_u03b1_3790_, lean_object* v_ref_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___redArg(v_ref_3791_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15___boxed(lean_object* v_00_u03b1_3800_, lean_object* v_ref_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__15(v_00_u03b1_3800_, v_ref_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4(lean_object* v_00_u03b1_3810_, lean_object* v_x_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v___x_3819_; 
v___x_3819_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v_x_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___boxed(lean_object* v_00_u03b1_3820_, lean_object* v_x_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4(v_00_u03b1_3820_, v_x_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5(lean_object* v_00_u03b1_3830_, lean_object* v_msg_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v_msg_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___boxed(lean_object* v_00_u03b1_3840_, lean_object* v_msg_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5(v_00_u03b1_3840_, v_msg_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6(lean_object* v_t_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v_t_3850_, v___y_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___boxed(lean_object* v_t_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6(v_t_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8(lean_object* v_env_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3868_, v___y_3872_, v___y_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___boxed(lean_object* v_env_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8(v_env_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3(lean_object* v_00_u03b1_3886_, lean_object* v_env_3887_, lean_object* v_x_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3887_, v_x_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3897_, lean_object* v_env_3898_, lean_object* v_x_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3(v_00_u03b1_3897_, v_env_3898_, v_x_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(lean_object* v_cls_3908_, lean_object* v_msg_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_cls_3908_, v_msg_3909_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___boxed(lean_object* v_cls_3918_, lean_object* v_msg_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(v_cls_3918_, v_msg_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(lean_object* v_as_3928_, lean_object* v_as_x27_3929_, lean_object* v_b_3930_, lean_object* v_a_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___redArg(v_as_x27_3929_, v_b_3930_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___boxed(lean_object* v_as_3940_, lean_object* v_as_x27_3941_, lean_object* v_b_3942_, lean_object* v_a_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(v_as_3940_, v_as_x27_3941_, v_b_3942_, v_a_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v_as_3940_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18(lean_object* v_msgData_3952_, lean_object* v_macroStack_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___redArg(v_msgData_3952_, v_macroStack_3953_, v___y_3958_);
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18___boxed(lean_object* v_msgData_3962_, lean_object* v_macroStack_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__18(v_msgData_3962_, v_macroStack_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20(lean_object* v_00_u03b2_3972_, lean_object* v_m_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___redArg(v_m_3973_, v_a_3974_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20___boxed(lean_object* v_00_u03b2_3976_, lean_object* v_m_3977_, lean_object* v_a_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20(v_00_u03b2_3976_, v_m_3977_, v_a_3978_);
lean_dec(v_a_3978_);
lean_dec_ref(v_m_3977_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18(lean_object* v_00_u03b1_3980_, lean_object* v_constName_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18___redArg(v_constName_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18___boxed(lean_object* v_00_u03b1_3990_, lean_object* v_constName_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18(v_00_u03b1_3990_, v_constName_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v___y_3997_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
return v_res_3999_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27(lean_object* v_00_u03b2_4000_, lean_object* v_x_4001_, lean_object* v_x_4002_){
_start:
{
uint8_t v___x_4003_; 
v___x_4003_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27___redArg(v_x_4001_, v_x_4002_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27___boxed(lean_object* v_00_u03b2_4004_, lean_object* v_x_4005_, lean_object* v_x_4006_){
_start:
{
uint8_t v_res_4007_; lean_object* v_r_4008_; 
v_res_4007_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27(v_00_u03b2_4004_, v_x_4005_, v_x_4006_);
lean_dec_ref(v_x_4006_);
v_r_4008_ = lean_box(v_res_4007_);
return v_r_4008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30(lean_object* v_00_u03b2_4009_, lean_object* v_a_4010_, lean_object* v_x_4011_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30___redArg(v_a_4010_, v_x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30___boxed(lean_object* v_00_u03b2_4013_, lean_object* v_a_4014_, lean_object* v_x_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__20_spec__30(v_00_u03b2_4013_, v_a_4014_, v_x_4015_);
lean_dec(v_x_4015_);
lean_dec(v_a_4014_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40(lean_object* v_00_u03b1_4017_, lean_object* v_x_4018_, uint8_t v_isExporting_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___redArg(v_x_4018_, v_isExporting_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40___boxed(lean_object* v_00_u03b1_4028_, lean_object* v_x_4029_, lean_object* v_isExporting_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
uint8_t v_isExporting_boxed_4038_; lean_object* v_res_4039_; 
v_isExporting_boxed_4038_ = lean_unbox(v_isExporting_4030_);
v_res_4039_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37_spec__40(v_00_u03b1_4028_, v_x_4029_, v_isExporting_boxed_4038_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37(lean_object* v_00_u03b1_4040_, lean_object* v_x_4041_, uint8_t v_when_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37___redArg(v_x_4041_, v_when_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37___boxed(lean_object* v_00_u03b1_4051_, lean_object* v_x_4052_, lean_object* v_when_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
uint8_t v_when_boxed_4061_; lean_object* v_res_4062_; 
v_when_boxed_4061_ = lean_unbox(v_when_4053_);
v_res_4062_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__32_spec__37(v_00_u03b1_4051_, v_x_4052_, v_when_boxed_4061_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29(lean_object* v_00_u03b1_4063_, lean_object* v_ref_4064_, lean_object* v_constName_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___redArg(v_ref_4064_, v_constName_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29___boxed(lean_object* v_00_u03b1_4074_, lean_object* v_ref_4075_, lean_object* v_constName_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29(v_00_u03b1_4074_, v_ref_4075_, v_constName_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec(v_ref_4075_);
return v_res_4084_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33(lean_object* v_00_u03b2_4085_, lean_object* v_x_4086_, size_t v_x_4087_, lean_object* v_x_4088_){
_start:
{
uint8_t v___x_4089_; 
v___x_4089_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___redArg(v_x_4086_, v_x_4087_, v_x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33___boxed(lean_object* v_00_u03b2_4090_, lean_object* v_x_4091_, lean_object* v_x_4092_, lean_object* v_x_4093_){
_start:
{
size_t v_x_59402__boxed_4094_; uint8_t v_res_4095_; lean_object* v_r_4096_; 
v_x_59402__boxed_4094_ = lean_unbox_usize(v_x_4092_);
lean_dec(v_x_4092_);
v_res_4095_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33(v_00_u03b2_4090_, v_x_4091_, v_x_59402__boxed_4094_, v_x_4093_);
lean_dec_ref(v_x_4093_);
v_r_4096_ = lean_box(v_res_4095_);
return v_r_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43(lean_object* v_ref_4097_, lean_object* v_msgData_4098_, uint8_t v_severity_4099_, uint8_t v_isSilent_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___redArg(v_ref_4097_, v_msgData_4098_, v_severity_4099_, v_isSilent_4100_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43___boxed(lean_object* v_ref_4109_, lean_object* v_msgData_4110_, lean_object* v_severity_4111_, lean_object* v_isSilent_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
uint8_t v_severity_boxed_4120_; uint8_t v_isSilent_boxed_4121_; lean_object* v_res_4122_; 
v_severity_boxed_4120_ = lean_unbox(v_severity_4111_);
v_isSilent_boxed_4121_ = lean_unbox(v_isSilent_4112_);
v_res_4122_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__23_spec__33_spec__39_spec__43(v_ref_4109_, v_msgData_4110_, v_severity_boxed_4120_, v_isSilent_boxed_4121_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v_ref_4109_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38(lean_object* v_00_u03b1_4123_, lean_object* v_ref_4124_, lean_object* v_msg_4125_, lean_object* v_declHint_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38___redArg(v_ref_4124_, v_msg_4125_, v_declHint_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38___boxed(lean_object* v_00_u03b1_4135_, lean_object* v_ref_4136_, lean_object* v_msg_4137_, lean_object* v_declHint_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38(v_00_u03b1_4135_, v_ref_4136_, v_msg_4137_, v_declHint_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec(v_ref_4136_);
return v_res_4146_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41(lean_object* v_00_u03b2_4147_, lean_object* v_keys_4148_, lean_object* v_vals_4149_, lean_object* v_heq_4150_, lean_object* v_i_4151_, lean_object* v_k_4152_){
_start:
{
uint8_t v___x_4153_; 
v___x_4153_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41___redArg(v_keys_4148_, v_i_4151_, v_k_4152_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41___boxed(lean_object* v_00_u03b2_4154_, lean_object* v_keys_4155_, lean_object* v_vals_4156_, lean_object* v_heq_4157_, lean_object* v_i_4158_, lean_object* v_k_4159_){
_start:
{
uint8_t v_res_4160_; lean_object* v_r_4161_; 
v_res_4160_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12_spec__18_spec__27_spec__33_spec__41(v_00_u03b2_4154_, v_keys_4155_, v_vals_4156_, v_heq_4157_, v_i_4158_, v_k_4159_);
lean_dec_ref(v_k_4159_);
lean_dec_ref(v_vals_4156_);
lean_dec_ref(v_keys_4155_);
v_r_4161_ = lean_box(v_res_4160_);
return v_r_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49(lean_object* v_msg_4162_, lean_object* v_declHint_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___redArg(v_msg_4162_, v_declHint_4163_, v___y_4169_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49___boxed(lean_object* v_msg_4172_, lean_object* v_declHint_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__18_spec__29_spec__38_spec__45_spec__49(v_msg_4172_, v_declHint_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0(lean_object* v_k_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v_b_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = lean_apply_8(v_k_4182_, v_b_4185_, v___y_4183_, v___y_4184_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, lean_box(0));
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v_b_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0(v_k_4192_, v___y_4193_, v___y_4194_, v_b_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(lean_object* v_shortDeclName_4202_, lean_object* v_type_4203_, lean_object* v_declName_4204_, lean_object* v_k_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v___f_4213_; lean_object* v___x_4214_; 
v___f_4213_ = lean_alloc_closure((void*)(l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4213_, 0, v_k_4205_);
lean_closure_set(v___f_4213_, 1, v___y_4206_);
lean_closure_set(v___f_4213_, 2, v___y_4207_);
v___x_4214_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withAuxDeclImp(lean_box(0), v_shortDeclName_4202_, v_type_4203_, v_declName_4204_, v___f_4213_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
if (lean_obj_tag(v___x_4214_) == 0)
{
return v___x_4214_;
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4214_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4214_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___boxed(lean_object* v_shortDeclName_4223_, lean_object* v_type_4224_, lean_object* v_declName_4225_, lean_object* v_k_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4223_, v_type_4224_, v_declName_4225_, v_k_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0(lean_object* v_00_u03b1_4235_, lean_object* v_shortDeclName_4236_, lean_object* v_type_4237_, lean_object* v_declName_4238_, lean_object* v_k_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4236_, v_type_4237_, v_declName_4238_, v_k_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___boxed(lean_object* v_00_u03b1_4248_, lean_object* v_shortDeclName_4249_, lean_object* v_type_4250_, lean_object* v_declName_4251_, lean_object* v_k_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0(v_00_u03b1_4248_, v_shortDeclName_4249_, v_type_4250_, v_declName_4251_, v_k_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0___boxed(lean_object* v_i_4261_, lean_object* v_fvars_4262_, lean_object* v_views_4263_, lean_object* v_k_4264_, lean_object* v_fvar_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0(v_i_4261_, v_fvars_4262_, v_views_4263_, v_k_4264_, v_fvar_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
lean_dec(v_i_4261_);
return v_res_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(lean_object* v_views_4274_, lean_object* v_k_4275_, lean_object* v_i_4276_, lean_object* v_fvars_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v___x_4285_; uint8_t v___x_4286_; 
v___x_4285_ = lean_array_get_size(v_views_4274_);
v___x_4286_ = lean_nat_dec_lt(v_i_4276_, v___x_4285_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; 
lean_dec(v_i_4276_);
lean_dec_ref(v_views_4274_);
v___x_4287_ = lean_apply_8(v_k_4275_, v_fvars_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, lean_box(0));
return v___x_4287_;
}
else
{
lean_object* v_view_4288_; lean_object* v_shortDeclName_4289_; lean_object* v_declName_4290_; lean_object* v_type_4291_; lean_object* v___f_4292_; lean_object* v___x_4293_; 
v_view_4288_ = lean_array_fget_borrowed(v_views_4274_, v_i_4276_);
v_shortDeclName_4289_ = lean_ctor_get(v_view_4288_, 2);
lean_inc(v_shortDeclName_4289_);
v_declName_4290_ = lean_ctor_get(v_view_4288_, 3);
lean_inc(v_declName_4290_);
v_type_4291_ = lean_ctor_get(v_view_4288_, 7);
lean_inc_ref(v_type_4291_);
v___f_4292_ = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4292_, 0, v_i_4276_);
lean_closure_set(v___f_4292_, 1, v_fvars_4277_);
lean_closure_set(v___f_4292_, 2, v_views_4274_);
lean_closure_set(v___f_4292_, 3, v_k_4275_);
v___x_4293_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4289_, v_type_4291_, v_declName_4290_, v___f_4292_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
return v___x_4293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0(lean_object* v_i_4294_, lean_object* v_fvars_4295_, lean_object* v_views_4296_, lean_object* v_k_4297_, lean_object* v_fvar_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4306_ = lean_unsigned_to_nat(1u);
v___x_4307_ = lean_nat_add(v_i_4294_, v___x_4306_);
v___x_4308_ = lean_array_push(v_fvars_4295_, v_fvar_4298_);
v___x_4309_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4296_, v_k_4297_, v___x_4307_, v___x_4308_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___boxed(lean_object* v_views_4310_, lean_object* v_k_4311_, lean_object* v_i_4312_, lean_object* v_fvars_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4310_, v_k_4311_, v_i_4312_, v_fvars_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(lean_object* v_00_u03b1_4322_, lean_object* v_views_4323_, lean_object* v_k_4324_, lean_object* v_i_4325_, lean_object* v_fvars_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4323_, v_k_4324_, v_i_4325_, v_fvars_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___boxed(lean_object* v_00_u03b1_4335_, lean_object* v_views_4336_, lean_object* v_k_4337_, lean_object* v_i_4338_, lean_object* v_fvars_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(v_00_u03b1_4335_, v_views_4336_, v_k_4337_, v_i_4338_, v_fvars_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(lean_object* v_views_4350_, lean_object* v_k_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4359_ = lean_unsigned_to_nat(0u);
v___x_4360_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___closed__0));
v___x_4361_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4350_, v_k_4351_, v___x_4359_, v___x_4360_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___boxed(lean_object* v_views_4362_, lean_object* v_k_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_views_4362_, v_k_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(lean_object* v_00_u03b1_4372_, lean_object* v_views_4373_, lean_object* v_k_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_views_4373_, v_k_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___boxed(lean_object* v_00_u03b1_4383_, lean_object* v_views_4384_, lean_object* v_k_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(v_00_u03b1_4383_, v_views_4384_, v_k_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0(lean_object* v_k_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v_b_4397_, lean_object* v_c_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_apply_9(v_k_4394_, v_b_4397_, v_c_4398_, v___y_4395_, v___y_4396_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, lean_box(0));
return v___x_4404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0___boxed(lean_object* v_k_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v_b_4408_, lean_object* v_c_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0(v_k_4405_, v___y_4406_, v___y_4407_, v_b_4408_, v_c_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(lean_object* v_type_4416_, lean_object* v_maxFVars_x3f_4417_, lean_object* v_k_4418_, uint8_t v_cleanupAnnotations_4419_, uint8_t v_whnfType_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v___f_4428_; lean_object* v___x_4429_; 
v___f_4428_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4428_, 0, v_k_4418_);
lean_closure_set(v___f_4428_, 1, v___y_4421_);
lean_closure_set(v___f_4428_, 2, v___y_4422_);
v___x_4429_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4416_, v_maxFVars_x3f_4417_, v___f_4428_, v_cleanupAnnotations_4419_, v_whnfType_4420_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
if (lean_obj_tag(v___x_4429_) == 0)
{
return v___x_4429_;
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4429_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4429_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___boxed(lean_object* v_type_4438_, lean_object* v_maxFVars_x3f_4439_, lean_object* v_k_4440_, lean_object* v_cleanupAnnotations_4441_, lean_object* v_whnfType_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4450_; uint8_t v_whnfType_boxed_4451_; lean_object* v_res_4452_; 
v_cleanupAnnotations_boxed_4450_ = lean_unbox(v_cleanupAnnotations_4441_);
v_whnfType_boxed_4451_ = lean_unbox(v_whnfType_4442_);
v_res_4452_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4438_, v_maxFVars_x3f_4439_, v_k_4440_, v_cleanupAnnotations_boxed_4450_, v_whnfType_boxed_4451_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1(lean_object* v_00_u03b1_4453_, lean_object* v_type_4454_, lean_object* v_maxFVars_x3f_4455_, lean_object* v_k_4456_, uint8_t v_cleanupAnnotations_4457_, uint8_t v_whnfType_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4454_, v_maxFVars_x3f_4455_, v_k_4456_, v_cleanupAnnotations_4457_, v_whnfType_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___boxed(lean_object* v_00_u03b1_4467_, lean_object* v_type_4468_, lean_object* v_maxFVars_x3f_4469_, lean_object* v_k_4470_, lean_object* v_cleanupAnnotations_4471_, lean_object* v_whnfType_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4480_; uint8_t v_whnfType_boxed_4481_; lean_object* v_res_4482_; 
v_cleanupAnnotations_boxed_4480_ = lean_unbox(v_cleanupAnnotations_4471_);
v_whnfType_boxed_4481_ = lean_unbox(v_whnfType_4472_);
v_res_4482_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1(v_00_u03b1_4467_, v_type_4468_, v_maxFVars_x3f_4469_, v_k_4470_, v_cleanupAnnotations_boxed_4480_, v_whnfType_boxed_4481_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0(lean_object* v_valStx_4483_, lean_object* v_x_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; 
v___x_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4492_, 0, v_x_4484_);
v___x_4493_ = l_Lean_Elab_Term_mkBodyInfo(v_valStx_4483_, v___x_4492_);
v___x_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4493_);
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0___boxed(lean_object* v_valStx_4496_, lean_object* v_x_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0(v_valStx_4496_, v_x_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(lean_object* v_upperBound_4506_, lean_object* v___x_4507_, lean_object* v_xs_4508_, lean_object* v_a_4509_, lean_object* v_b_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
uint8_t v___x_4518_; 
v___x_4518_ = lean_nat_dec_lt(v_a_4509_, v_upperBound_4506_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; 
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v_a_4509_);
v___x_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4519_, 0, v_b_4510_);
return v___x_4519_;
}
else
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4520_ = l_Lean_instInhabitedExpr;
v___x_4521_ = lean_array_fget_borrowed(v___x_4507_, v_a_4509_);
v___x_4522_ = lean_array_get_borrowed(v___x_4520_, v_xs_4508_, v_a_4509_);
lean_inc(v___y_4516_);
lean_inc_ref(v___y_4515_);
lean_inc(v___y_4514_);
lean_inc_ref(v___y_4513_);
lean_inc(v___y_4512_);
lean_inc_ref(v___y_4511_);
lean_inc(v___x_4522_);
lean_inc(v___x_4521_);
v___x_4523_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_4521_, v___x_4522_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
lean_dec_ref(v___x_4523_);
v___x_4524_ = lean_box(0);
v___x_4525_ = lean_unsigned_to_nat(1u);
v___x_4526_ = lean_nat_add(v_a_4509_, v___x_4525_);
lean_dec(v_a_4509_);
v_a_4509_ = v___x_4526_;
v_b_4510_ = v___x_4524_;
goto _start;
}
else
{
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4515_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v_a_4509_);
return v___x_4523_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg___boxed(lean_object* v_upperBound_4528_, lean_object* v___x_4529_, lean_object* v_xs_4530_, lean_object* v_a_4531_, lean_object* v_b_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v_upperBound_4528_, v___x_4529_, v_xs_4530_, v_a_4531_, v_b_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec_ref(v_xs_4530_);
lean_dec_ref(v___x_4529_);
lean_dec(v_upperBound_4528_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1(lean_object* v_valStx_4541_, lean_object* v___x_4542_, uint8_t v___x_4543_, lean_object* v___x_4544_, lean_object* v_xs_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v___x_4553_; 
lean_inc(v___y_4551_);
lean_inc_ref(v___y_4550_);
lean_inc(v___y_4549_);
lean_inc_ref(v___y_4548_);
v___x_4553_ = l_Lean_Elab_Term_elabTermEnsuringType(v_valStx_4541_, v___x_4542_, v___x_4543_, v___x_4543_, v___x_4544_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; uint8_t v___x_4555_; uint8_t v___x_4556_; lean_object* v___x_4557_; 
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4554_);
lean_dec_ref(v___x_4553_);
v___x_4555_ = 0;
v___x_4556_ = 1;
v___x_4557_ = l_Lean_Meta_mkLambdaFVars(v_xs_4545_, v_a_4554_, v___x_4555_, v___x_4543_, v___x_4555_, v___x_4543_, v___x_4556_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
return v___x_4557_;
}
else
{
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
return v___x_4553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1___boxed(lean_object* v_valStx_4558_, lean_object* v___x_4559_, lean_object* v___x_4560_, lean_object* v___x_4561_, lean_object* v_xs_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
uint8_t v___x_3255__boxed_4570_; lean_object* v_res_4571_; 
v___x_3255__boxed_4570_ = lean_unbox(v___x_4560_);
v_res_4571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1(v_valStx_4558_, v___x_4559_, v___x_3255__boxed_4570_, v___x_4561_, v_xs_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec_ref(v_xs_4562_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2(lean_object* v___x_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v___x_4580_; 
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4572_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2___boxed(lean_object* v___x_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2(v___x_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3(lean_object* v___x_4590_, lean_object* v_binderIds_4591_, lean_object* v_valStx_4592_, uint8_t v___x_4593_, lean_object* v___f_4594_, lean_object* v_declName_4595_, lean_object* v_xs_4596_, lean_object* v_type_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4605_ = lean_unsigned_to_nat(0u);
v___x_4606_ = lean_box(0);
lean_inc(v___y_4603_);
lean_inc_ref(v___y_4602_);
lean_inc(v___y_4601_);
lean_inc_ref(v___y_4600_);
lean_inc(v___y_4599_);
lean_inc_ref(v___y_4598_);
v___x_4607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v___x_4590_, v_binderIds_4591_, v_xs_4596_, v___x_4605_, v___x_4606_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___f_4611_; lean_object* v___x_4612_; lean_object* v___f_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
lean_dec_ref(v___x_4607_);
v___x_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4608_, 0, v_type_4597_);
v___x_4609_ = lean_box(0);
v___x_4610_ = lean_box(v___x_4593_);
lean_inc(v_valStx_4592_);
v___f_4611_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4611_, 0, v_valStx_4592_);
lean_closure_set(v___f_4611_, 1, v___x_4608_);
lean_closure_set(v___f_4611_, 2, v___x_4610_);
lean_closure_set(v___f_4611_, 3, v___x_4609_);
lean_closure_set(v___f_4611_, 4, v_xs_4596_);
lean_inc(v_valStx_4592_);
v___x_4612_ = l_Lean_Elab_Term_mkBodyInfo(v_valStx_4592_, v___x_4609_);
v___f_4613_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2___boxed), 8, 1);
lean_closure_set(v___f_4613_, 0, v___x_4612_);
v___x_4614_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withInfoContext_x27___boxed), 11, 4);
lean_closure_set(v___x_4614_, 0, v_valStx_4592_);
lean_closure_set(v___x_4614_, 1, v___f_4611_);
lean_closure_set(v___x_4614_, 2, v___f_4594_);
lean_closure_set(v___x_4614_, 3, v___f_4613_);
v___x_4615_ = l_Lean_Elab_Term_withDeclName___redArg(v_declName_4595_, v___x_4614_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
return v___x_4615_;
}
else
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4623_; 
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec_ref(v_type_4597_);
lean_dec_ref(v_xs_4596_);
lean_dec(v_declName_4595_);
lean_dec_ref(v___f_4594_);
lean_dec(v_valStx_4592_);
v_a_4616_ = lean_ctor_get(v___x_4607_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4618_ = v___x_4607_;
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4607_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4621_; 
if (v_isShared_4619_ == 0)
{
v___x_4621_ = v___x_4618_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4616_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3___boxed(lean_object* v___x_4624_, lean_object* v_binderIds_4625_, lean_object* v_valStx_4626_, lean_object* v___x_4627_, lean_object* v___f_4628_, lean_object* v_declName_4629_, lean_object* v_xs_4630_, lean_object* v_type_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
uint8_t v___x_3322__boxed_4639_; lean_object* v_res_4640_; 
v___x_3322__boxed_4639_ = lean_unbox(v___x_4627_);
v_res_4640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3(v___x_4624_, v_binderIds_4625_, v_valStx_4626_, v___x_3322__boxed_4639_, v___f_4628_, v_declName_4629_, v_xs_4630_, v_type_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
lean_dec_ref(v_binderIds_4625_);
lean_dec(v___x_4624_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(size_t v_sz_4641_, size_t v_i_4642_, lean_object* v_bs_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
uint8_t v___x_4651_; 
v___x_4651_ = lean_usize_dec_lt(v_i_4642_, v_sz_4641_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4652_; 
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_bs_4643_);
return v___x_4652_;
}
else
{
lean_object* v_v_4653_; lean_object* v_declName_4654_; lean_object* v_binderIds_4655_; lean_object* v_type_4656_; lean_object* v_valStx_4657_; lean_object* v___f_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___f_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; lean_object* v___x_4664_; 
v_v_4653_ = lean_array_uget_borrowed(v_bs_4643_, v_i_4642_);
v_declName_4654_ = lean_ctor_get(v_v_4653_, 3);
v_binderIds_4655_ = lean_ctor_get(v_v_4653_, 5);
v_type_4656_ = lean_ctor_get(v_v_4653_, 7);
v_valStx_4657_ = lean_ctor_get(v_v_4653_, 9);
lean_inc(v_valStx_4657_);
v___f_4658_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4658_, 0, v_valStx_4657_);
v___x_4659_ = lean_array_get_size(v_binderIds_4655_);
v___x_4660_ = lean_box(v___x_4651_);
lean_inc(v_declName_4654_);
lean_inc(v_valStx_4657_);
lean_inc_ref(v_binderIds_4655_);
v___f_4661_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3___boxed), 15, 6);
lean_closure_set(v___f_4661_, 0, v___x_4659_);
lean_closure_set(v___f_4661_, 1, v_binderIds_4655_);
lean_closure_set(v___f_4661_, 2, v_valStx_4657_);
lean_closure_set(v___f_4661_, 3, v___x_4660_);
lean_closure_set(v___f_4661_, 4, v___f_4658_);
lean_closure_set(v___f_4661_, 5, v_declName_4654_);
v___x_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4659_);
v___x_4663_ = 0;
lean_inc(v___y_4649_);
lean_inc_ref(v___y_4648_);
lean_inc(v___y_4647_);
lean_inc_ref(v___y_4646_);
lean_inc(v___y_4645_);
lean_inc_ref(v___y_4644_);
lean_inc_ref(v_type_4656_);
v___x_4664_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4656_, v___x_4662_, v___f_4661_, v___x_4651_, v___x_4663_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4666_; lean_object* v_bs_x27_4667_; size_t v___x_4668_; size_t v___x_4669_; lean_object* v___x_4670_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref(v___x_4664_);
v___x_4666_ = lean_unsigned_to_nat(0u);
v_bs_x27_4667_ = lean_array_uset(v_bs_4643_, v_i_4642_, v___x_4666_);
v___x_4668_ = ((size_t)1ULL);
v___x_4669_ = lean_usize_add(v_i_4642_, v___x_4668_);
v___x_4670_ = lean_array_uset(v_bs_x27_4667_, v_i_4642_, v_a_4665_);
v_i_4642_ = v___x_4669_;
v_bs_4643_ = v___x_4670_;
goto _start;
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec_ref(v_bs_4643_);
v_a_4672_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4664_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4664_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___boxed(lean_object* v_sz_4680_, lean_object* v_i_4681_, lean_object* v_bs_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
size_t v_sz_boxed_4690_; size_t v_i_boxed_4691_; lean_object* v_res_4692_; 
v_sz_boxed_4690_ = lean_unbox_usize(v_sz_4680_);
lean_dec(v_sz_4680_);
v_i_boxed_4691_ = lean_unbox_usize(v_i_4681_);
lean_dec(v_i_4681_);
v_res_4692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(v_sz_boxed_4690_, v_i_boxed_4691_, v_bs_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_);
return v_res_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(lean_object* v_view_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
lean_object* v_decls_4701_; size_t v_sz_4702_; size_t v___x_4703_; lean_object* v___x_4704_; 
v_decls_4701_ = lean_ctor_get(v_view_4693_, 0);
lean_inc_ref(v_decls_4701_);
lean_dec_ref(v_view_4693_);
v_sz_4702_ = lean_array_size(v_decls_4701_);
v___x_4703_ = ((size_t)0ULL);
v___x_4704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(v_sz_4702_, v___x_4703_, v_decls_4701_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___boxed(lean_object* v_view_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(v_view_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0(lean_object* v_upperBound_4714_, lean_object* v___x_4715_, lean_object* v_xs_4716_, lean_object* v_inst_4717_, lean_object* v_R_4718_, lean_object* v_a_4719_, lean_object* v_b_4720_, lean_object* v_c_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v___x_4729_; 
v___x_4729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v_upperBound_4714_, v___x_4715_, v_xs_4716_, v_a_4719_, v_b_4720_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___boxed(lean_object* v_upperBound_4730_, lean_object* v___x_4731_, lean_object* v_xs_4732_, lean_object* v_inst_4733_, lean_object* v_R_4734_, lean_object* v_a_4735_, lean_object* v_b_4736_, lean_object* v_c_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0(v_upperBound_4730_, v___x_4731_, v_xs_4732_, v_inst_4733_, v_R_4734_, v_a_4735_, v_b_4736_, v_c_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
lean_dec_ref(v_xs_4732_);
lean_dec_ref(v___x_4731_);
lean_dec(v_upperBound_4730_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___redArg(lean_object* v_values_4746_, lean_object* v_fvars_4747_, lean_object* v___x_4748_, lean_object* v_a_4749_, lean_object* v_as_4750_, lean_object* v_i_4751_, lean_object* v_j_4752_, lean_object* v_bs_4753_){
_start:
{
lean_object* v_zero_4755_; uint8_t v_isZero_4756_; 
v_zero_4755_ = lean_unsigned_to_nat(0u);
v_isZero_4756_ = lean_nat_dec_eq(v_i_4751_, v_zero_4755_);
if (v_isZero_4756_ == 1)
{
lean_object* v___x_4757_; 
lean_dec(v_j_4752_);
lean_dec(v_i_4751_);
lean_dec_ref(v_a_4749_);
lean_dec_ref(v___x_4748_);
v___x_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4757_, 0, v_bs_4753_);
return v___x_4757_;
}
else
{
lean_object* v___x_4758_; lean_object* v_ref_4759_; lean_object* v_attrs_4760_; lean_object* v_shortDeclName_4761_; lean_object* v_declName_4762_; lean_object* v_parentName_x3f_4763_; lean_object* v_binderIds_4764_; lean_object* v_binders_4765_; lean_object* v_type_4766_; lean_object* v_mvar_4767_; lean_object* v_termination_4768_; lean_object* v_docString_x3f_4769_; lean_object* v___x_4770_; lean_object* v_one_4771_; lean_object* v_n_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4758_ = lean_array_fget_borrowed(v_as_4750_, v_j_4752_);
v_ref_4759_ = lean_ctor_get(v___x_4758_, 0);
v_attrs_4760_ = lean_ctor_get(v___x_4758_, 1);
v_shortDeclName_4761_ = lean_ctor_get(v___x_4758_, 2);
v_declName_4762_ = lean_ctor_get(v___x_4758_, 3);
v_parentName_x3f_4763_ = lean_ctor_get(v___x_4758_, 4);
v_binderIds_4764_ = lean_ctor_get(v___x_4758_, 5);
v_binders_4765_ = lean_ctor_get(v___x_4758_, 6);
v_type_4766_ = lean_ctor_get(v___x_4758_, 7);
v_mvar_4767_ = lean_ctor_get(v___x_4758_, 8);
v_termination_4768_ = lean_ctor_get(v___x_4758_, 10);
v_docString_x3f_4769_ = lean_ctor_get(v___x_4758_, 11);
v___x_4770_ = l_Lean_instInhabitedExpr;
v_one_4771_ = lean_unsigned_to_nat(1u);
v_n_4772_ = lean_nat_sub(v_i_4751_, v_one_4771_);
lean_dec(v_i_4751_);
v___x_4773_ = lean_array_get_borrowed(v___x_4770_, v_values_4746_, v_j_4752_);
v___x_4774_ = lean_array_get_size(v_binderIds_4764_);
lean_inc_ref(v_termination_4768_);
v___x_4775_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v___x_4774_, v_termination_4768_, v___x_4773_);
v___x_4776_ = lean_array_get_borrowed(v___x_4770_, v_fvars_4747_, v_j_4752_);
v___x_4777_ = l_Lean_Expr_fvarId_x21(v___x_4776_);
v___x_4778_ = l_Lean_Expr_mvarId_x21(v_mvar_4767_);
lean_inc(v_docString_x3f_4769_);
lean_inc(v_binders_4765_);
lean_inc(v___x_4773_);
lean_inc_ref(v_type_4766_);
lean_inc_ref(v_a_4749_);
lean_inc_ref(v___x_4748_);
lean_inc(v_parentName_x3f_4763_);
lean_inc(v_declName_4762_);
lean_inc(v_shortDeclName_4761_);
lean_inc_ref(v_attrs_4760_);
lean_inc(v_ref_4759_);
v___x_4779_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v___x_4779_, 0, v_ref_4759_);
lean_ctor_set(v___x_4779_, 1, v___x_4777_);
lean_ctor_set(v___x_4779_, 2, v_attrs_4760_);
lean_ctor_set(v___x_4779_, 3, v_shortDeclName_4761_);
lean_ctor_set(v___x_4779_, 4, v_declName_4762_);
lean_ctor_set(v___x_4779_, 5, v_parentName_x3f_4763_);
lean_ctor_set(v___x_4779_, 6, v___x_4748_);
lean_ctor_set(v___x_4779_, 7, v_a_4749_);
lean_ctor_set(v___x_4779_, 8, v_type_4766_);
lean_ctor_set(v___x_4779_, 9, v___x_4773_);
lean_ctor_set(v___x_4779_, 10, v___x_4778_);
lean_ctor_set(v___x_4779_, 11, v___x_4775_);
lean_ctor_set(v___x_4779_, 12, v_binders_4765_);
lean_ctor_set(v___x_4779_, 13, v_docString_x3f_4769_);
v___x_4780_ = lean_nat_add(v_j_4752_, v_one_4771_);
lean_dec(v_j_4752_);
v___x_4781_ = lean_array_push(v_bs_4753_, v___x_4779_);
v_i_4751_ = v_n_4772_;
v_j_4752_ = v___x_4780_;
v_bs_4753_ = v___x_4781_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___redArg___boxed(lean_object* v_values_4783_, lean_object* v_fvars_4784_, lean_object* v___x_4785_, lean_object* v_a_4786_, lean_object* v_as_4787_, lean_object* v_i_4788_, lean_object* v_j_4789_, lean_object* v_bs_4790_, lean_object* v___y_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___redArg(v_values_4783_, v_fvars_4784_, v___x_4785_, v_a_4786_, v_as_4787_, v_i_4788_, v_j_4789_, v_bs_4790_);
lean_dec_ref(v_as_4787_);
lean_dec_ref(v_fvars_4784_);
lean_dec_ref(v_values_4783_);
return v_res_4792_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___lam__0(lean_object* v_a_4793_, lean_object* v_toLift_4794_){
_start:
{
lean_object* v_declName_4795_; lean_object* v_declName_4796_; uint8_t v___x_4797_; 
v_declName_4795_ = lean_ctor_get(v_toLift_4794_, 4);
v_declName_4796_ = lean_ctor_get(v_a_4793_, 3);
v___x_4797_ = lean_name_eq(v_declName_4795_, v_declName_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___lam__0___boxed(lean_object* v_a_4798_, lean_object* v_toLift_4799_){
_start:
{
uint8_t v_res_4800_; lean_object* v_r_4801_; 
v_res_4800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___lam__0(v_a_4798_, v_toLift_4799_);
lean_dec_ref(v_toLift_4799_);
lean_dec_ref(v_a_4798_);
v_r_4801_ = lean_box(v_res_4800_);
return v_r_4801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(lean_object* v___x_4802_, lean_object* v_as_4803_, size_t v_sz_4804_, size_t v_i_4805_, lean_object* v_b_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
lean_object* v_a_4815_; uint8_t v___x_4819_; 
v___x_4819_ = lean_usize_dec_lt(v_i_4805_, v_sz_4804_);
if (v___x_4819_ == 0)
{
lean_object* v___x_4820_; 
lean_dec_ref(v___y_4807_);
lean_dec(v___x_4802_);
v___x_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4820_, 0, v_b_4806_);
return v___x_4820_;
}
else
{
lean_object* v___x_4821_; lean_object* v_a_4822_; lean_object* v___f_4823_; uint8_t v___x_4824_; 
v___x_4821_ = lean_box(0);
v_a_4822_ = lean_array_uget_borrowed(v_as_4803_, v_i_4805_);
lean_inc(v_a_4822_);
v___f_4823_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4823_, 0, v_a_4822_);
lean_inc(v___x_4802_);
v___x_4824_ = l_List_any___redArg(v___x_4802_, v___f_4823_);
if (v___x_4824_ == 0)
{
v_a_4815_ = v___x_4821_;
goto v___jp_4814_;
}
else
{
lean_object* v_ref_4825_; lean_object* v_declName_4826_; lean_object* v_fileName_4827_; lean_object* v_fileMap_4828_; lean_object* v_options_4829_; lean_object* v_currRecDepth_4830_; lean_object* v_maxRecDepth_4831_; lean_object* v_ref_4832_; lean_object* v_currNamespace_4833_; lean_object* v_openDecls_4834_; lean_object* v_initHeartbeats_4835_; lean_object* v_maxHeartbeats_4836_; lean_object* v_quotContext_4837_; lean_object* v_currMacroScope_4838_; uint8_t v_diag_4839_; lean_object* v_cancelTk_x3f_4840_; uint8_t v_suppressElabErrors_4841_; lean_object* v_inheritedTraceOptions_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v_ref_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
v_ref_4825_ = lean_ctor_get(v_a_4822_, 0);
v_declName_4826_ = lean_ctor_get(v_a_4822_, 3);
v_fileName_4827_ = lean_ctor_get(v___y_4811_, 0);
v_fileMap_4828_ = lean_ctor_get(v___y_4811_, 1);
v_options_4829_ = lean_ctor_get(v___y_4811_, 2);
v_currRecDepth_4830_ = lean_ctor_get(v___y_4811_, 3);
v_maxRecDepth_4831_ = lean_ctor_get(v___y_4811_, 4);
v_ref_4832_ = lean_ctor_get(v___y_4811_, 5);
v_currNamespace_4833_ = lean_ctor_get(v___y_4811_, 6);
v_openDecls_4834_ = lean_ctor_get(v___y_4811_, 7);
v_initHeartbeats_4835_ = lean_ctor_get(v___y_4811_, 8);
v_maxHeartbeats_4836_ = lean_ctor_get(v___y_4811_, 9);
v_quotContext_4837_ = lean_ctor_get(v___y_4811_, 10);
v_currMacroScope_4838_ = lean_ctor_get(v___y_4811_, 11);
v_diag_4839_ = lean_ctor_get_uint8(v___y_4811_, sizeof(void*)*14);
v_cancelTk_x3f_4840_ = lean_ctor_get(v___y_4811_, 12);
v_suppressElabErrors_4841_ = lean_ctor_get_uint8(v___y_4811_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4842_ = lean_ctor_get(v___y_4811_, 13);
v___x_4843_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
lean_inc(v_declName_4826_);
v___x_4844_ = l_Lean_MessageData_ofName(v_declName_4826_);
v___x_4845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4843_);
lean_ctor_set(v___x_4845_, 1, v___x_4844_);
v___x_4846_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_4847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4845_);
lean_ctor_set(v___x_4847_, 1, v___x_4846_);
v_ref_4848_ = l_Lean_replaceRef(v_ref_4825_, v_ref_4832_);
lean_inc_ref(v_inheritedTraceOptions_4842_);
lean_inc(v_cancelTk_x3f_4840_);
lean_inc(v_currMacroScope_4838_);
lean_inc(v_quotContext_4837_);
lean_inc(v_maxHeartbeats_4836_);
lean_inc(v_initHeartbeats_4835_);
lean_inc(v_openDecls_4834_);
lean_inc(v_currNamespace_4833_);
lean_inc(v_maxRecDepth_4831_);
lean_inc(v_currRecDepth_4830_);
lean_inc_ref(v_options_4829_);
lean_inc_ref(v_fileMap_4828_);
lean_inc_ref(v_fileName_4827_);
v___x_4849_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4849_, 0, v_fileName_4827_);
lean_ctor_set(v___x_4849_, 1, v_fileMap_4828_);
lean_ctor_set(v___x_4849_, 2, v_options_4829_);
lean_ctor_set(v___x_4849_, 3, v_currRecDepth_4830_);
lean_ctor_set(v___x_4849_, 4, v_maxRecDepth_4831_);
lean_ctor_set(v___x_4849_, 5, v_ref_4848_);
lean_ctor_set(v___x_4849_, 6, v_currNamespace_4833_);
lean_ctor_set(v___x_4849_, 7, v_openDecls_4834_);
lean_ctor_set(v___x_4849_, 8, v_initHeartbeats_4835_);
lean_ctor_set(v___x_4849_, 9, v_maxHeartbeats_4836_);
lean_ctor_set(v___x_4849_, 10, v_quotContext_4837_);
lean_ctor_set(v___x_4849_, 11, v_currMacroScope_4838_);
lean_ctor_set(v___x_4849_, 12, v_cancelTk_x3f_4840_);
lean_ctor_set(v___x_4849_, 13, v_inheritedTraceOptions_4842_);
lean_ctor_set_uint8(v___x_4849_, sizeof(void*)*14, v_diag_4839_);
lean_ctor_set_uint8(v___x_4849_, sizeof(void*)*14 + 1, v_suppressElabErrors_4841_);
lean_inc_ref(v___y_4807_);
v___x_4850_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_4847_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___x_4849_, v___y_4812_);
lean_dec_ref(v___x_4849_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_dec_ref(v___x_4850_);
v_a_4815_ = v___x_4821_;
goto v___jp_4814_;
}
else
{
lean_dec_ref(v___y_4807_);
lean_dec(v___x_4802_);
return v___x_4850_;
}
}
}
v___jp_4814_:
{
size_t v___x_4816_; size_t v___x_4817_; 
v___x_4816_ = ((size_t)1ULL);
v___x_4817_ = lean_usize_add(v_i_4805_, v___x_4816_);
v_i_4805_ = v___x_4817_;
v_b_4806_ = v_a_4815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___boxed(lean_object* v___x_4851_, lean_object* v_as_4852_, lean_object* v_sz_4853_, lean_object* v_i_4854_, lean_object* v_b_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
size_t v_sz_boxed_4863_; size_t v_i_boxed_4864_; lean_object* v_res_4865_; 
v_sz_boxed_4863_ = lean_unbox_usize(v_sz_4853_);
lean_dec(v_sz_4853_);
v_i_boxed_4864_ = lean_unbox_usize(v_i_4854_);
lean_dec(v_i_4854_);
v_res_4865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(v___x_4851_, v_as_4852_, v_sz_boxed_4863_, v_i_boxed_4864_, v_b_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v_as_4852_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(lean_object* v_views_4866_, lean_object* v_fvars_4867_, lean_object* v_values_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_){
_start:
{
lean_object* v___x_4876_; lean_object* v_letRecsToLift_4877_; lean_object* v___x_4878_; size_t v_sz_4879_; size_t v___x_4880_; lean_object* v___x_4881_; 
v___x_4876_ = lean_st_ref_get(v_a_4870_);
v_letRecsToLift_4877_ = lean_ctor_get(v___x_4876_, 6);
lean_inc(v_letRecsToLift_4877_);
lean_dec(v___x_4876_);
v___x_4878_ = lean_box(0);
v_sz_4879_ = lean_array_size(v_views_4866_);
v___x_4880_ = ((size_t)0ULL);
v___x_4881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(v_letRecsToLift_4877_, v_views_4866_, v_sz_4879_, v___x_4880_, v___x_4878_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v___x_4882_; 
lean_dec_ref(v___x_4881_);
v___x_4882_ = l_Lean_Meta_getLocalInstances___redArg(v_a_4871_);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v_a_4883_; lean_object* v_lctx_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4914_; 
v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
lean_inc(v_a_4883_);
lean_dec_ref(v___x_4882_);
v_lctx_4884_ = lean_ctor_get(v_a_4871_, 2);
lean_inc_ref(v_lctx_4884_);
lean_dec_ref(v_a_4871_);
v___x_4885_ = lean_array_get_size(v_views_4866_);
v___x_4886_ = lean_unsigned_to_nat(0u);
v___x_4887_ = lean_mk_empty_array_with_capacity(v___x_4885_);
v___x_4888_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___redArg(v_values_4868_, v_fvars_4867_, v_lctx_4884_, v_a_4883_, v_views_4866_, v___x_4885_, v___x_4886_, v___x_4887_);
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4891_ = v___x_4888_;
v_isShared_4892_ = v_isSharedCheck_4914_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4888_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4914_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4893_; lean_object* v_levelNames_4894_; lean_object* v_syntheticMVars_4895_; lean_object* v_pendingMVars_4896_; lean_object* v_mvarErrorInfos_4897_; lean_object* v_levelMVarErrorInfos_4898_; lean_object* v_mvarArgNames_4899_; lean_object* v_letRecsToLift_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4913_; 
v___x_4893_ = lean_st_ref_take(v_a_4870_);
v_levelNames_4894_ = lean_ctor_get(v___x_4893_, 0);
v_syntheticMVars_4895_ = lean_ctor_get(v___x_4893_, 1);
v_pendingMVars_4896_ = lean_ctor_get(v___x_4893_, 2);
v_mvarErrorInfos_4897_ = lean_ctor_get(v___x_4893_, 3);
v_levelMVarErrorInfos_4898_ = lean_ctor_get(v___x_4893_, 4);
v_mvarArgNames_4899_ = lean_ctor_get(v___x_4893_, 5);
v_letRecsToLift_4900_ = lean_ctor_get(v___x_4893_, 6);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4902_ = v___x_4893_;
v_isShared_4903_ = v_isSharedCheck_4913_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_letRecsToLift_4900_);
lean_inc(v_mvarArgNames_4899_);
lean_inc(v_levelMVarErrorInfos_4898_);
lean_inc(v_mvarErrorInfos_4897_);
lean_inc(v_pendingMVars_4896_);
lean_inc(v_syntheticMVars_4895_);
lean_inc(v_levelNames_4894_);
lean_dec(v___x_4893_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4913_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4907_; 
v___x_4904_ = lean_array_to_list(v_a_4889_);
v___x_4905_ = l_List_appendTR___redArg(v___x_4904_, v_letRecsToLift_4900_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 6, v___x_4905_);
v___x_4907_ = v___x_4902_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v_levelNames_4894_);
lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_syntheticMVars_4895_);
lean_ctor_set(v_reuseFailAlloc_4912_, 2, v_pendingMVars_4896_);
lean_ctor_set(v_reuseFailAlloc_4912_, 3, v_mvarErrorInfos_4897_);
lean_ctor_set(v_reuseFailAlloc_4912_, 4, v_levelMVarErrorInfos_4898_);
lean_ctor_set(v_reuseFailAlloc_4912_, 5, v_mvarArgNames_4899_);
lean_ctor_set(v_reuseFailAlloc_4912_, 6, v___x_4905_);
v___x_4907_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4908_; lean_object* v___x_4910_; 
v___x_4908_ = lean_st_ref_set(v_a_4870_, v___x_4907_);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 0, v___x_4878_);
v___x_4910_ = v___x_4891_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4878_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
lean_dec_ref(v_a_4871_);
v_a_4915_ = lean_ctor_get(v___x_4882_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4882_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4882_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
else
{
lean_dec_ref(v_a_4871_);
return v___x_4881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___boxed(lean_object* v_views_4923_, lean_object* v_fvars_4924_, lean_object* v_values_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(v_views_4923_, v_fvars_4924_, v_values_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
lean_dec(v_a_4929_);
lean_dec(v_a_4927_);
lean_dec_ref(v_values_4925_);
lean_dec_ref(v_fvars_4924_);
lean_dec_ref(v_views_4923_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(lean_object* v_values_4934_, lean_object* v_fvars_4935_, lean_object* v___x_4936_, lean_object* v_a_4937_, lean_object* v_as_4938_, lean_object* v_i_4939_, lean_object* v_j_4940_, lean_object* v_inv_4941_, lean_object* v_bs_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___redArg(v_values_4934_, v_fvars_4935_, v___x_4936_, v_a_4937_, v_as_4938_, v_i_4939_, v_j_4940_, v_bs_4942_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___boxed(lean_object* v_values_4951_, lean_object* v_fvars_4952_, lean_object* v___x_4953_, lean_object* v_a_4954_, lean_object* v_as_4955_, lean_object* v_i_4956_, lean_object* v_j_4957_, lean_object* v_inv_4958_, lean_object* v_bs_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(v_values_4951_, v_fvars_4952_, v___x_4953_, v_a_4954_, v_as_4955_, v_i_4956_, v_j_4957_, v_inv_4958_, v_bs_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
lean_dec_ref(v_as_4955_);
lean_dec_ref(v_fvars_4952_);
lean_dec_ref(v_values_4951_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(size_t v_sz_4968_, size_t v_i_4969_, lean_object* v_bs_4970_){
_start:
{
uint8_t v___x_4971_; 
v___x_4971_ = lean_usize_dec_lt(v_i_4969_, v_sz_4968_);
if (v___x_4971_ == 0)
{
return v_bs_4970_;
}
else
{
lean_object* v_v_4972_; lean_object* v_mvar_4973_; lean_object* v___x_4974_; lean_object* v_bs_x27_4975_; size_t v___x_4976_; size_t v___x_4977_; lean_object* v___x_4978_; 
v_v_4972_ = lean_array_uget_borrowed(v_bs_4970_, v_i_4969_);
v_mvar_4973_ = lean_ctor_get(v_v_4972_, 8);
lean_inc_ref(v_mvar_4973_);
v___x_4974_ = lean_unsigned_to_nat(0u);
v_bs_x27_4975_ = lean_array_uset(v_bs_4970_, v_i_4969_, v___x_4974_);
v___x_4976_ = ((size_t)1ULL);
v___x_4977_ = lean_usize_add(v_i_4969_, v___x_4976_);
v___x_4978_ = lean_array_uset(v_bs_x27_4975_, v_i_4969_, v_mvar_4973_);
v_i_4969_ = v___x_4977_;
v_bs_4970_ = v___x_4978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1___boxed(lean_object* v_sz_4980_, lean_object* v_i_4981_, lean_object* v_bs_4982_){
_start:
{
size_t v_sz_boxed_4983_; size_t v_i_boxed_4984_; lean_object* v_res_4985_; 
v_sz_boxed_4983_ = lean_unbox_usize(v_sz_4980_);
lean_dec(v_sz_4980_);
v_i_boxed_4984_ = lean_unbox_usize(v_i_4981_);
lean_dec(v_i_4981_);
v_res_4985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(v_sz_boxed_4983_, v_i_boxed_4984_, v_bs_4982_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(lean_object* v_as_4986_, size_t v_sz_4987_, size_t v_i_4988_, lean_object* v_b_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_){
_start:
{
uint8_t v___x_4997_; 
v___x_4997_ = lean_usize_dec_lt(v_i_4988_, v_sz_4987_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; 
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec(v___y_4991_);
lean_dec_ref(v___y_4990_);
v___x_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4998_, 0, v_b_4989_);
return v___x_4998_;
}
else
{
lean_object* v_array_4999_; lean_object* v_start_5000_; lean_object* v_stop_5001_; uint8_t v___x_5002_; 
v_array_4999_ = lean_ctor_get(v_b_4989_, 0);
v_start_5000_ = lean_ctor_get(v_b_4989_, 1);
v_stop_5001_ = lean_ctor_get(v_b_4989_, 2);
v___x_5002_ = lean_nat_dec_lt(v_start_5000_, v_stop_5001_);
if (v___x_5002_ == 0)
{
lean_object* v___x_5003_; 
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec(v___y_4991_);
lean_dec_ref(v___y_4990_);
v___x_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5003_, 0, v_b_4989_);
return v___x_5003_;
}
else
{
lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5027_; 
lean_inc(v_stop_5001_);
lean_inc(v_start_5000_);
lean_inc_ref(v_array_4999_);
v_isSharedCheck_5027_ = !lean_is_exclusive(v_b_4989_);
if (v_isSharedCheck_5027_ == 0)
{
lean_object* v_unused_5028_; lean_object* v_unused_5029_; lean_object* v_unused_5030_; 
v_unused_5028_ = lean_ctor_get(v_b_4989_, 2);
lean_dec(v_unused_5028_);
v_unused_5029_ = lean_ctor_get(v_b_4989_, 1);
lean_dec(v_unused_5029_);
v_unused_5030_ = lean_ctor_get(v_b_4989_, 0);
lean_dec(v_unused_5030_);
v___x_5005_ = v_b_4989_;
v_isShared_5006_ = v_isSharedCheck_5027_;
goto v_resetjp_5004_;
}
else
{
lean_dec(v_b_4989_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5027_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v_a_5007_; lean_object* v_ref_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v_a_5007_ = lean_array_uget_borrowed(v_as_4986_, v_i_4988_);
v_ref_5008_ = lean_ctor_get(v_a_5007_, 0);
v___x_5009_ = lean_array_fget_borrowed(v_array_4999_, v_start_5000_);
lean_inc(v___y_4995_);
lean_inc_ref(v___y_4994_);
lean_inc(v___y_4993_);
lean_inc_ref(v___y_4992_);
lean_inc(v___y_4991_);
lean_inc_ref(v___y_4990_);
lean_inc(v___x_5009_);
lean_inc(v_ref_5008_);
v___x_5010_ = l_Lean_Elab_Term_addLocalVarInfo(v_ref_5008_, v___x_5009_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5014_; 
lean_dec_ref(v___x_5010_);
v___x_5011_ = lean_unsigned_to_nat(1u);
v___x_5012_ = lean_nat_add(v_start_5000_, v___x_5011_);
lean_dec(v_start_5000_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 1, v___x_5012_);
v___x_5014_ = v___x_5005_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_array_4999_);
lean_ctor_set(v_reuseFailAlloc_5018_, 1, v___x_5012_);
lean_ctor_set(v_reuseFailAlloc_5018_, 2, v_stop_5001_);
v___x_5014_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
size_t v___x_5015_; size_t v___x_5016_; 
v___x_5015_ = ((size_t)1ULL);
v___x_5016_ = lean_usize_add(v_i_4988_, v___x_5015_);
v_i_4988_ = v___x_5016_;
v_b_4989_ = v___x_5014_;
goto _start;
}
}
else
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
lean_del_object(v___x_5005_);
lean_dec(v_stop_5001_);
lean_dec(v_start_5000_);
lean_dec_ref(v_array_4999_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
lean_dec(v___y_4993_);
lean_dec_ref(v___y_4992_);
lean_dec(v___y_4991_);
lean_dec_ref(v___y_4990_);
v_a_5019_ = lean_ctor_get(v___x_5010_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5010_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_5010_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_5010_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0___boxed(lean_object* v_as_5031_, lean_object* v_sz_5032_, lean_object* v_i_5033_, lean_object* v_b_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_){
_start:
{
size_t v_sz_boxed_5042_; size_t v_i_boxed_5043_; lean_object* v_res_5044_; 
v_sz_boxed_5042_ = lean_unbox_usize(v_sz_5032_);
lean_dec(v_sz_5032_);
v_i_boxed_5043_ = lean_unbox_usize(v_i_5033_);
lean_dec(v_i_5033_);
v_res_5044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(v_as_5031_, v_sz_boxed_5042_, v_i_boxed_5043_, v_b_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_);
lean_dec_ref(v_as_5031_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0(lean_object* v_decls_5045_, lean_object* v_a_5046_, lean_object* v_body_5047_, lean_object* v_expectedType_x3f_5048_, lean_object* v_fvars_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; size_t v_sz_5060_; size_t v___x_5061_; lean_object* v___x_5062_; 
v___x_5057_ = lean_unsigned_to_nat(0u);
v___x_5058_ = lean_array_get_size(v_fvars_5049_);
lean_inc_ref(v_fvars_5049_);
v___x_5059_ = l_Array_toSubarray___redArg(v_fvars_5049_, v___x_5057_, v___x_5058_);
v_sz_5060_ = lean_array_size(v_decls_5045_);
v___x_5061_ = ((size_t)0ULL);
lean_inc(v___y_5055_);
lean_inc_ref(v___y_5054_);
lean_inc(v___y_5053_);
lean_inc_ref(v___y_5052_);
lean_inc(v___y_5051_);
lean_inc_ref(v___y_5050_);
v___x_5062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(v_decls_5045_, v_sz_5060_, v___x_5061_, v___x_5059_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v___x_5063_; 
lean_dec_ref(v___x_5062_);
lean_inc(v___y_5055_);
lean_inc_ref(v___y_5054_);
lean_inc(v___y_5053_);
lean_inc_ref(v___y_5052_);
lean_inc(v___y_5051_);
lean_inc_ref(v___y_5050_);
v___x_5063_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(v_a_5046_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v_a_5064_; uint8_t v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_a_5064_);
lean_dec_ref(v___x_5063_);
v___x_5065_ = 1;
v___x_5066_ = lean_box(0);
lean_inc(v___y_5055_);
lean_inc_ref(v___y_5054_);
lean_inc(v___y_5053_);
lean_inc_ref(v___y_5052_);
lean_inc(v___y_5051_);
lean_inc_ref(v___y_5050_);
v___x_5067_ = l_Lean_Elab_Term_elabTermEnsuringType(v_body_5047_, v_expectedType_x3f_5048_, v___x_5065_, v___x_5065_, v___x_5066_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v_a_5068_; lean_object* v___x_5069_; 
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_a_5068_);
lean_dec_ref(v___x_5067_);
lean_inc_ref(v___y_5052_);
v___x_5069_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(v_decls_5045_, v_fvars_5049_, v_a_5064_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec(v___y_5051_);
lean_dec(v_a_5064_);
if (lean_obj_tag(v___x_5069_) == 0)
{
uint8_t v___x_5070_; uint8_t v___x_5071_; lean_object* v___x_5072_; 
lean_dec_ref(v___x_5069_);
v___x_5070_ = 0;
v___x_5071_ = 1;
v___x_5072_ = l_Lean_Meta_mkLambdaFVars(v_fvars_5049_, v_a_5068_, v___x_5070_, v___x_5065_, v___x_5070_, v___x_5065_, v___x_5071_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec_ref(v_fvars_5049_);
if (lean_obj_tag(v___x_5072_) == 0)
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5082_; 
v_a_5073_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5075_ = v___x_5072_;
v_isShared_5076_ = v_isSharedCheck_5082_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5072_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5082_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5080_; 
v___x_5077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(v_sz_5060_, v___x_5061_, v_decls_5045_);
v___x_5078_ = l_Lean_mkAppN(v_a_5073_, v___x_5077_);
lean_dec_ref(v___x_5077_);
if (v_isShared_5076_ == 0)
{
lean_ctor_set(v___x_5075_, 0, v___x_5078_);
v___x_5080_ = v___x_5075_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5078_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
else
{
lean_dec_ref(v_decls_5045_);
return v___x_5072_;
}
}
else
{
lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5090_; 
lean_dec(v_a_5068_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec_ref(v_fvars_5049_);
lean_dec_ref(v_decls_5045_);
v_a_5083_ = lean_ctor_get(v___x_5069_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5069_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_5069_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_dec(v___x_5069_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5088_; 
if (v_isShared_5086_ == 0)
{
v___x_5088_ = v___x_5085_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_a_5083_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
}
else
{
lean_dec(v_a_5064_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec_ref(v_fvars_5049_);
lean_dec_ref(v_decls_5045_);
return v___x_5067_;
}
}
else
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5098_; 
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec_ref(v_fvars_5049_);
lean_dec(v_expectedType_x3f_5048_);
lean_dec(v_body_5047_);
lean_dec_ref(v_decls_5045_);
v_a_5091_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5093_ = v___x_5063_;
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v___x_5063_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5098_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v___x_5096_; 
if (v_isShared_5094_ == 0)
{
v___x_5096_ = v___x_5093_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5097_; 
v_reuseFailAlloc_5097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5091_);
v___x_5096_ = v_reuseFailAlloc_5097_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
return v___x_5096_;
}
}
}
}
else
{
lean_object* v_a_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5106_; 
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec_ref(v_fvars_5049_);
lean_dec(v_expectedType_x3f_5048_);
lean_dec(v_body_5047_);
lean_dec_ref(v_a_5046_);
lean_dec_ref(v_decls_5045_);
v_a_5099_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5106_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5101_ = v___x_5062_;
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_a_5099_);
lean_dec(v___x_5062_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5106_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5104_; 
if (v_isShared_5102_ == 0)
{
v___x_5104_ = v___x_5101_;
goto v_reusejp_5103_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
v___x_5104_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5103_;
}
v_reusejp_5103_:
{
return v___x_5104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0___boxed(lean_object* v_decls_5107_, lean_object* v_a_5108_, lean_object* v_body_5109_, lean_object* v_expectedType_x3f_5110_, lean_object* v_fvars_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Lean_Elab_Term_elabLetRec___lam__0(v_decls_5107_, v_a_5108_, v_body_5109_, v_expectedType_x3f_5110_, v_fvars_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec(lean_object* v_stx_5120_, lean_object* v_expectedType_x3f_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v___x_5129_; 
lean_inc(v_a_5127_);
lean_inc_ref(v_a_5126_);
lean_inc(v_a_5125_);
lean_inc_ref(v_a_5124_);
lean_inc(v_a_5123_);
lean_inc_ref(v_a_5122_);
v___x_5129_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(v_stx_5120_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v_decls_5131_; lean_object* v_body_5132_; lean_object* v___f_5133_; lean_object* v___x_5134_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref(v___x_5129_);
v_decls_5131_ = lean_ctor_get(v_a_5130_, 0);
lean_inc_ref(v_decls_5131_);
v_body_5132_ = lean_ctor_get(v_a_5130_, 1);
lean_inc(v_body_5132_);
lean_inc_ref(v_decls_5131_);
v___f_5133_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetRec___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5133_, 0, v_decls_5131_);
lean_closure_set(v___f_5133_, 1, v_a_5130_);
lean_closure_set(v___f_5133_, 2, v_body_5132_);
lean_closure_set(v___f_5133_, 3, v_expectedType_x3f_5121_);
v___x_5134_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_decls_5131_, v___f_5133_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_);
return v___x_5134_;
}
else
{
lean_object* v_a_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5142_; 
lean_dec(v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_a_5125_);
lean_dec_ref(v_a_5124_);
lean_dec(v_a_5123_);
lean_dec_ref(v_a_5122_);
lean_dec(v_expectedType_x3f_5121_);
v_a_5135_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5137_ = v___x_5129_;
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_a_5135_);
lean_dec(v___x_5129_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5140_; 
if (v_isShared_5138_ == 0)
{
v___x_5140_ = v___x_5137_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___boxed(lean_object* v_stx_5143_, lean_object* v_expectedType_x3f_5144_, lean_object* v_a_5145_, lean_object* v_a_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_Lean_Elab_Term_elabLetRec(v_stx_5143_, v_expectedType_x3f_5144_, v_a_5145_, v_a_5146_, v_a_5147_, v_a_5148_, v_a_5149_, v_a_5150_);
lean_dec(v_stx_5143_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1(){
_start:
{
lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v___x_5166_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5167_ = ((lean_object*)(l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1));
v___x_5168_ = ((lean_object*)(l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3));
v___x_5169_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetRec___boxed), 9, 0);
v___x_5170_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5166_, v___x_5167_, v___x_5168_, v___x_5169_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___boxed(lean_object* v_a_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1();
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3(){
_start:
{
lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v___x_5199_ = ((lean_object*)(l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3));
v___x_5200_ = ((lean_object*)(l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6));
v___x_5201_ = l_Lean_addBuiltinDeclarationRanges(v___x_5199_, v___x_5200_);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___boxed(lean_object* v_a_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3();
return v_res_5203_;
}
}
lean_object* runtime_initialize_Lean_Elab_MutualDef(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_LetRec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_MutualDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_LetRec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_MutualDef(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_LetRec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_MutualDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_LetRec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_LetRec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_LetRec(builtin);
}
#ifdef __cplusplus
}
#endif
