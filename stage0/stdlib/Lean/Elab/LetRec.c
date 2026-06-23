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
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
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
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withAuxDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkBodyInfo(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withInfoContext_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_TerminationHints_rememberExtraParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_doc_verso;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
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
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBindersEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
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
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__0 = (const lean_object*)&l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot use attribute `["};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "]`: module `"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "` is loaded for IR only (reached as a private `meta` dependency). Add an import of `"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Unknown attribute `["};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]`"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__12_value;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__13_value;
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14_value;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unknown attribute"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__4_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letEqnsDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "letrec"};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 19, 234, 96, 193, 73, 5, 238)}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabLetRec"};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(101, 182, 190, 124, 44, 87, 65, 222)}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(132) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__0_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__1_value),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(34) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(123) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__3_value),((lean_object*)(((size_t)(34) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__4_value),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___boxed(lean_object*);
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
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
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
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__0(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(1);
v___x_42_ = l_Lean_MessageData_ofFormat(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__3(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__2));
v___x_47_ = l_Lean_MessageData_ofFormat(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26(lean_object* v_x_48_, lean_object* v_x_49_){
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
v___x_59_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__0);
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
v___x_62_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__3);
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
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__2(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__1));
v___x_78_ = l_Lean_MessageData_ofFormat(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg(lean_object* v_msgData_79_, lean_object* v_macroStack_80_, lean_object* v___y_81_){
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
v___x_93_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26___closed__0);
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
v___x_96_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___closed__2);
v___x_97_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = l_Lean_MessageData_ofSyntax(v_after_89_);
v___x_99_ = l_Lean_indentD(v___x_98_);
v_msgData_100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_100_, 0, v___x_97_);
lean_ctor_set(v_msgData_100_, 1, v___x_99_);
v___x_101_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17_spec__26(v_msgData_100_, v_macroStack_80_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg___boxed(lean_object* v_msgData_106_, lean_object* v_macroStack_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg(v_msgData_106_, v_macroStack_107_, v___y_108_);
lean_dec_ref(v___y_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16(lean_object* v_msgData_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16___boxed(lean_object* v_msgData_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16(v_msgData_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
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
v___x_142_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16(v_msg_133_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref(v___x_142_);
v_macroStack_144_ = lean_ctor_get(v___y_134_, 1);
v___x_145_ = l_Lean_Elab_getBetterRef(v_ref_141_, v_macroStack_144_);
lean_inc(v_macroStack_144_);
v___x_146_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg(v_a_143_, v_macroStack_144_, v___y_138_);
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
lean_dec_ref(v___y_157_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(lean_object* v_ref_165_, lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_fileName_174_; lean_object* v_fileMap_175_; lean_object* v_options_176_; lean_object* v_currRecDepth_177_; lean_object* v_maxRecDepth_178_; lean_object* v_ref_179_; lean_object* v_currNamespace_180_; lean_object* v_openDecls_181_; lean_object* v_initHeartbeats_182_; lean_object* v_maxHeartbeats_183_; lean_object* v_quotContext_184_; lean_object* v_currMacroScope_185_; uint8_t v_diag_186_; lean_object* v_cancelTk_x3f_187_; uint8_t v_suppressElabErrors_188_; lean_object* v_inheritedTraceOptions_189_; lean_object* v_ref_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
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
v_ref_190_ = l_Lean_replaceRef(v_ref_165_, v_ref_179_);
lean_inc_ref(v_inheritedTraceOptions_189_);
lean_inc(v_cancelTk_x3f_187_);
lean_inc(v_currMacroScope_185_);
lean_inc(v_quotContext_184_);
lean_inc(v_maxHeartbeats_183_);
lean_inc(v_initHeartbeats_182_);
lean_inc(v_openDecls_181_);
lean_inc(v_currNamespace_180_);
lean_inc(v_maxRecDepth_178_);
lean_inc(v_currRecDepth_177_);
lean_inc_ref(v_options_176_);
lean_inc_ref(v_fileMap_175_);
lean_inc_ref(v_fileName_174_);
v___x_191_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_191_, 0, v_fileName_174_);
lean_ctor_set(v___x_191_, 1, v_fileMap_175_);
lean_ctor_set(v___x_191_, 2, v_options_176_);
lean_ctor_set(v___x_191_, 3, v_currRecDepth_177_);
lean_ctor_set(v___x_191_, 4, v_maxRecDepth_178_);
lean_ctor_set(v___x_191_, 5, v_ref_190_);
lean_ctor_set(v___x_191_, 6, v_currNamespace_180_);
lean_ctor_set(v___x_191_, 7, v_openDecls_181_);
lean_ctor_set(v___x_191_, 8, v_initHeartbeats_182_);
lean_ctor_set(v___x_191_, 9, v_maxHeartbeats_183_);
lean_ctor_set(v___x_191_, 10, v_quotContext_184_);
lean_ctor_set(v___x_191_, 11, v_currMacroScope_185_);
lean_ctor_set(v___x_191_, 12, v_cancelTk_x3f_187_);
lean_ctor_set(v___x_191_, 13, v_inheritedTraceOptions_189_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*14, v_diag_186_);
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*14 + 1, v_suppressElabErrors_188_);
v___x_192_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v_msg_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___x_191_, v___y_172_);
lean_dec_ref_known(v___x_191_, 14);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg___boxed(lean_object* v_ref_193_, lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_ref_193_, v_msg_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v_ref_193_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(lean_object* v_stx_203_, lean_object* v___y_204_){
_start:
{
uint8_t v___x_206_; lean_object* v___x_207_; 
v___x_206_ = 0;
v___x_207_ = l_Lean_Syntax_getRange_x3f(v_stx_203_, v___x_206_);
if (lean_obj_tag(v___x_207_) == 1)
{
lean_object* v_val_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_220_; 
v_val_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_220_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_val_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_fileMap_212_; lean_object* v_start_213_; lean_object* v_stop_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v_fileMap_212_ = lean_ctor_get(v___y_204_, 1);
v_start_213_ = lean_ctor_get(v_val_208_, 0);
lean_inc(v_start_213_);
v_stop_214_ = lean_ctor_get(v_val_208_, 1);
lean_inc(v_stop_214_);
lean_dec(v_val_208_);
lean_inc_ref(v_fileMap_212_);
v___x_215_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_212_, v_start_213_, v_stop_214_);
lean_dec(v_stop_214_);
lean_dec(v_start_213_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_215_);
v___x_217_ = v___x_210_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_219_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; 
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
return v___x_218_;
}
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v___x_207_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg___boxed(lean_object* v_stx_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_stx_223_, v___y_224_);
lean_dec_ref(v___y_224_);
lean_dec(v_stx_223_);
return v_res_226_;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_227_;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__0);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__1);
v___x_233_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
lean_ctor_set(v___x_233_, 2, v___x_232_);
lean_ctor_set(v___x_233_, 3, v___x_232_);
lean_ctor_set(v___x_233_, 4, v___x_232_);
lean_ctor_set(v___x_233_, 5, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(lean_object* v_declName_234_, lean_object* v_declRanges_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = l_Lean_Name_isAnonymous(v_declName_234_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v_env_241_; lean_object* v_nextMacroScope_242_; lean_object* v_ngen_243_; lean_object* v_auxDeclNGen_244_; lean_object* v_traceState_245_; lean_object* v_messages_246_; lean_object* v_infoState_247_; lean_object* v_snapshotTasks_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_276_; 
v___x_240_ = lean_st_ref_take(v___y_237_);
v_env_241_ = lean_ctor_get(v___x_240_, 0);
v_nextMacroScope_242_ = lean_ctor_get(v___x_240_, 1);
v_ngen_243_ = lean_ctor_get(v___x_240_, 2);
v_auxDeclNGen_244_ = lean_ctor_get(v___x_240_, 3);
v_traceState_245_ = lean_ctor_get(v___x_240_, 4);
v_messages_246_ = lean_ctor_get(v___x_240_, 6);
v_infoState_247_ = lean_ctor_get(v___x_240_, 7);
v_snapshotTasks_248_ = lean_ctor_get(v___x_240_, 8);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v___x_240_, 5);
lean_dec(v_unused_277_);
v___x_250_ = v___x_240_;
v_isShared_251_ = v_isSharedCheck_276_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_snapshotTasks_248_);
lean_inc(v_infoState_247_);
lean_inc(v_messages_246_);
lean_inc(v_traceState_245_);
lean_inc(v_auxDeclNGen_244_);
lean_inc(v_ngen_243_);
lean_inc(v_nextMacroScope_242_);
lean_inc(v_env_241_);
lean_dec(v___x_240_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_276_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_252_ = l_Lean_declRangeExt;
v___x_253_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_252_, v_env_241_, v_declName_234_, v_declRanges_235_);
v___x_254_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 5, v___x_254_);
lean_ctor_set(v___x_250_, 0, v___x_253_);
v___x_256_ = v___x_250_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_nextMacroScope_242_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_ngen_243_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_auxDeclNGen_244_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_traceState_245_);
lean_ctor_set(v_reuseFailAlloc_275_, 5, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_275_, 6, v_messages_246_);
lean_ctor_set(v_reuseFailAlloc_275_, 7, v_infoState_247_);
lean_ctor_set(v_reuseFailAlloc_275_, 8, v_snapshotTasks_248_);
v___x_256_ = v_reuseFailAlloc_275_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_mctx_259_; lean_object* v_zetaDeltaFVarIds_260_; lean_object* v_postponed_261_; lean_object* v_diag_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_273_; 
v___x_257_ = lean_st_ref_set(v___y_237_, v___x_256_);
v___x_258_ = lean_st_ref_take(v___y_236_);
v_mctx_259_ = lean_ctor_get(v___x_258_, 0);
v_zetaDeltaFVarIds_260_ = lean_ctor_get(v___x_258_, 2);
v_postponed_261_ = lean_ctor_get(v___x_258_, 3);
v_diag_262_ = lean_ctor_get(v___x_258_, 4);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v___x_258_, 1);
lean_dec(v_unused_274_);
v___x_264_ = v___x_258_;
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_diag_262_);
lean_inc(v_postponed_261_);
lean_inc(v_zetaDeltaFVarIds_260_);
lean_inc(v_mctx_259_);
lean_dec(v___x_258_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 1, v___x_266_);
v___x_268_ = v___x_264_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_mctx_259_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_zetaDeltaFVarIds_260_);
lean_ctor_set(v_reuseFailAlloc_272_, 3, v_postponed_261_);
lean_ctor_set(v_reuseFailAlloc_272_, 4, v_diag_262_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_st_ref_set(v___y_236_, v___x_268_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
}
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec_ref(v_declRanges_235_);
lean_dec(v_declName_234_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___boxed(lean_object* v_declName_280_, lean_object* v_declRanges_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_280_, v_declRanges_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec(v___y_282_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(lean_object* v_declName_286_, lean_object* v_rangeStx_287_, lean_object* v_selectionRangeStx_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_313_; 
v___x_296_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_rangeStx_287_, v___y_293_);
v_a_297_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_313_ == 0)
{
v___x_299_ = v___x_296_;
v_isShared_300_ = v_isSharedCheck_313_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_313_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
if (lean_obj_tag(v_a_297_) == 1)
{
lean_object* v_val_301_; lean_object* v___x_302_; lean_object* v_a_303_; lean_object* v_a_305_; 
lean_del_object(v___x_299_);
v_val_301_ = lean_ctor_get(v_a_297_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v_a_297_, 1);
v___x_302_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_selectionRangeStx_288_, v___y_293_);
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref(v___x_302_);
if (lean_obj_tag(v_a_303_) == 0)
{
lean_inc(v_val_301_);
v_a_305_ = v_val_301_;
goto v___jp_304_;
}
else
{
lean_object* v_val_308_; 
v_val_308_ = lean_ctor_get(v_a_303_, 0);
lean_inc(v_val_308_);
lean_dec_ref_known(v_a_303_, 1);
v_a_305_ = v_val_308_;
goto v___jp_304_;
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_val_301_);
lean_ctor_set(v___x_306_, 1, v_a_305_);
v___x_307_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_286_, v___x_306_, v___y_292_, v___y_294_);
return v___x_307_;
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_311_; 
lean_dec(v_a_297_);
lean_dec(v_declName_286_);
v___x_309_ = lean_box(0);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_309_);
v___x_311_ = v___x_299_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2___boxed(lean_object* v_declName_314_, lean_object* v_rangeStx_315_, lean_object* v_selectionRangeStx_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(v_declName_314_, v_rangeStx_315_, v_selectionRangeStx_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v_selectionRangeStx_316_);
lean_dec(v_rangeStx_315_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0(lean_object* v___x_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_325_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0___boxed(lean_object* v___x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0(v___x_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7(lean_object* v_00_u03b1_343_, lean_object* v_ref_344_, lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_ref_344_, v_msg_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___boxed(lean_object* v_00_u03b1_354_, lean_object* v_ref_355_, lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7(v_00_u03b1_354_, v_ref_355_, v_msg_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v_ref_355_);
return v_res_364_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__9));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__18));
v___x_407_ = l_Lean_stringToMessageData(v___x_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__20));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(lean_object* v_stx_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
if (lean_obj_tag(v_stx_423_) == 0)
{
lean_object* v___x_431_; lean_object* v_terminationBy_x3f_x3f_432_; lean_object* v_terminationBy_x3f_433_; lean_object* v_partialFixpoint_x3f_434_; lean_object* v_decreasingBy_x3f_435_; lean_object* v_extraParams_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_431_ = l_Lean_Elab_TerminationHints_none;
v_terminationBy_x3f_x3f_432_ = lean_ctor_get(v___x_431_, 1);
v_terminationBy_x3f_433_ = lean_ctor_get(v___x_431_, 2);
v_partialFixpoint_x3f_434_ = lean_ctor_get(v___x_431_, 3);
v_decreasingBy_x3f_435_ = lean_ctor_get(v___x_431_, 4);
v_extraParams_436_ = lean_ctor_get(v___x_431_, 5);
lean_inc(v_extraParams_436_);
lean_inc(v_decreasingBy_x3f_435_);
lean_inc(v_partialFixpoint_x3f_434_);
lean_inc(v_terminationBy_x3f_433_);
lean_inc(v_terminationBy_x3f_x3f_432_);
v___x_437_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_437_, 0, v_stx_423_);
lean_ctor_set(v___x_437_, 1, v_terminationBy_x3f_x3f_432_);
lean_ctor_set(v___x_437_, 2, v_terminationBy_x3f_433_);
lean_ctor_set(v___x_437_, 3, v_partialFixpoint_x3f_434_);
lean_ctor_set(v___x_437_, 4, v_decreasingBy_x3f_435_);
lean_ctor_set(v___x_437_, 5, v_extraParams_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4));
lean_inc(v_stx_423_);
v___x_440_ = l_Lean_Syntax_isOfKind(v_stx_423_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_441_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_442_ = lean_box(0);
lean_inc_n(v_stx_423_, 2);
v___x_443_ = l_Lean_Syntax_formatStx(v_stx_423_, v___x_442_, v___x_440_);
v___x_444_ = l_Std_Format_defWidth;
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = l_Std_Format_pretty(v___x_443_, v___x_444_, v___x_445_, v___x_445_);
v___x_447_ = lean_string_append(v___x_441_, v___x_446_);
lean_dec_ref(v___x_446_);
v___x_448_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_449_ = lean_string_append(v___x_447_, v___x_448_);
v___x_450_ = l_Lean_Syntax_getKind(v_stx_423_);
v___x_451_ = 1;
v___x_452_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_450_, v___x_451_);
v___x_453_ = lean_string_append(v___x_449_, v___x_452_);
lean_dec_ref(v___x_452_);
v___x_454_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
v___x_455_ = l_Lean_MessageData_ofFormat(v___x_454_);
v___x_456_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_423_, v___x_455_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v_stx_423_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v_partialFixpoint_x3f_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v_term_x3f_523_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v_term_x3f_539_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v_term_x3f_555_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v_val_562_; lean_object* v___y_563_; lean_object* v_terminationBy_x3f_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v_terminationBy_x3f_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_617_; uint8_t v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; uint8_t v___y_630_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; uint8_t v___y_685_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v_s_700_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v_val_735_; lean_object* v___y_736_; lean_object* v_terminationBy_x3f_x3f_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v_d_x3f_826_; lean_object* v_t_x3f_835_; lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_873_ = l_Lean_Syntax_getArg(v_stx_423_, v___x_457_);
v___x_874_ = l_Lean_Syntax_isNone(v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_873_);
v___x_876_ = l_Lean_Syntax_matchesNull(v___x_873_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v___x_873_);
v___x_877_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_878_ = lean_box(0);
lean_inc_n(v_stx_423_, 2);
v___x_879_ = l_Lean_Syntax_formatStx(v_stx_423_, v___x_878_, v___x_876_);
v___x_880_ = l_Std_Format_defWidth;
v___x_881_ = l_Std_Format_pretty(v___x_879_, v___x_880_, v___x_457_, v___x_457_);
v___x_882_ = lean_string_append(v___x_877_, v___x_881_);
lean_dec_ref(v___x_881_);
v___x_883_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_884_ = lean_string_append(v___x_882_, v___x_883_);
v___x_885_ = l_Lean_Syntax_getKind(v_stx_423_);
v___x_886_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_885_, v___x_440_);
v___x_887_ = lean_string_append(v___x_884_, v___x_886_);
lean_dec_ref(v___x_886_);
v___x_888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
v___x_889_ = l_Lean_MessageData_ofFormat(v___x_888_);
v___x_890_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_423_, v___x_889_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v_stx_423_);
return v___x_890_;
}
else
{
lean_object* v_t_x3f_891_; lean_object* v___x_892_; 
v_t_x3f_891_ = l_Lean_Syntax_getArg(v___x_873_, v___x_457_);
lean_dec(v___x_873_);
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v_t_x3f_891_);
v_t_x3f_835_ = v___x_892_;
goto v___jp_834_;
}
}
else
{
lean_object* v___x_893_; 
lean_dec(v___x_873_);
v___x_893_ = lean_box(0);
v_t_x3f_835_ = v___x_893_;
goto v___jp_834_;
}
v___jp_458_:
{
lean_object* v___x_469_; 
lean_inc(v___y_461_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_460_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_467_);
v___x_469_ = lean_apply_7(v___y_468_, v___y_467_, v___y_464_, v___y_466_, v___y_460_, v___y_463_, v___y_461_, lean_box(0));
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_479_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v_a_470_);
v___x_475_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_475_, 0, v_stx_423_);
lean_ctor_set(v___x_475_, 1, v___y_462_);
lean_ctor_set(v___x_475_, 2, v___y_465_);
lean_ctor_set(v___x_475_, 3, v___y_459_);
lean_ctor_set(v___x_475_, 4, v___x_474_);
lean_ctor_set(v___x_475_, 5, v___x_457_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v___y_465_);
lean_dec(v___y_462_);
lean_dec(v___y_459_);
lean_dec(v_stx_423_);
v_a_480_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_469_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_469_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
v___jp_488_:
{
if (lean_obj_tag(v___y_490_) == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_box(0);
v___x_501_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_501_, 0, v_stx_423_);
lean_ctor_set(v___x_501_, 1, v___y_489_);
lean_ctor_set(v___x_501_, 2, v___y_492_);
lean_ctor_set(v___x_501_, 3, v_partialFixpoint_x3f_493_);
lean_ctor_set(v___x_501_, 4, v___x_500_);
lean_ctor_set(v___x_501_, 5, v___x_457_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_val_503_ = lean_ctor_get(v___y_490_, 0);
lean_inc_n(v_val_503_, 2);
lean_dec_ref_known(v___y_490_, 1);
v___x_504_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8));
v___x_505_ = l_Lean_Syntax_isOfKind(v_val_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10);
v___x_507_ = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___boxed), 10, 3);
lean_closure_set(v___x_507_, 0, lean_box(0));
lean_closure_set(v___x_507_, 1, v_val_503_);
lean_closure_set(v___x_507_, 2, v___x_506_);
v___y_459_ = v_partialFixpoint_x3f_493_;
v___y_460_ = v___y_497_;
v___y_461_ = v___y_499_;
v___y_462_ = v___y_489_;
v___y_463_ = v___y_498_;
v___y_464_ = v___y_495_;
v___y_465_ = v___y_492_;
v___y_466_ = v___y_496_;
v___y_467_ = v___y_494_;
v___y_468_ = v___x_507_;
goto v___jp_458_;
}
else
{
lean_object* v_tactic_508_; lean_object* v___x_509_; lean_object* v___f_510_; 
v_tactic_508_ = l_Lean_Syntax_getArg(v_val_503_, v___y_491_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_val_503_);
lean_ctor_set(v___x_509_, 1, v_tactic_508_);
v___f_510_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_510_, 0, v___x_509_);
v___y_459_ = v_partialFixpoint_x3f_493_;
v___y_460_ = v___y_497_;
v___y_461_ = v___y_499_;
v___y_462_ = v___y_489_;
v___y_463_ = v___y_498_;
v___y_464_ = v___y_495_;
v___y_465_ = v___y_492_;
v___y_466_ = v___y_496_;
v___y_467_ = v___y_494_;
v___y_468_ = v___f_510_;
goto v___jp_458_;
}
}
}
v___jp_511_:
{
uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = 0;
v___x_525_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_525_, 0, v___y_514_);
lean_ctor_set(v___x_525_, 1, v_term_x3f_523_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*2, v___x_524_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___y_489_ = v___y_517_;
v___y_490_ = v___y_516_;
v___y_491_ = v___y_519_;
v___y_492_ = v___y_521_;
v_partialFixpoint_x3f_493_ = v___x_526_;
v___y_494_ = v___y_513_;
v___y_495_ = v___y_522_;
v___y_496_ = v___y_515_;
v___y_497_ = v___y_520_;
v___y_498_ = v___y_512_;
v___y_499_ = v___y_518_;
goto v___jp_488_;
}
v___jp_527_:
{
uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = 1;
v___x_541_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_541_, 0, v___y_530_);
lean_ctor_set(v___x_541_, 1, v_term_x3f_539_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*2, v___x_540_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v___y_489_ = v___y_533_;
v___y_490_ = v___y_532_;
v___y_491_ = v___y_535_;
v___y_492_ = v___y_537_;
v_partialFixpoint_x3f_493_ = v___x_542_;
v___y_494_ = v___y_529_;
v___y_495_ = v___y_538_;
v___y_496_ = v___y_531_;
v___y_497_ = v___y_536_;
v___y_498_ = v___y_528_;
v___y_499_ = v___y_534_;
goto v___jp_488_;
}
v___jp_543_:
{
uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = 2;
v___x_557_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_557_, 0, v___y_546_);
lean_ctor_set(v___x_557_, 1, v_term_x3f_555_);
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*2, v___x_556_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___y_489_ = v___y_549_;
v___y_490_ = v___y_548_;
v___y_491_ = v___y_551_;
v___y_492_ = v___y_553_;
v_partialFixpoint_x3f_493_ = v___x_558_;
v___y_494_ = v___y_545_;
v___y_495_ = v___y_554_;
v___y_496_ = v___y_547_;
v___y_497_ = v___y_552_;
v___y_498_ = v___y_544_;
v___y_499_ = v___y_550_;
goto v___jp_488_;
}
v___jp_559_:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12));
lean_inc(v_val_562_);
v___x_572_ = l_Lean_Syntax_isOfKind(v_val_562_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14));
lean_inc(v_val_562_);
v___x_574_ = l_Lean_Syntax_isOfKind(v_val_562_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16));
lean_inc(v_val_562_);
v___x_576_ = l_Lean_Syntax_isOfKind(v_val_562_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v_val_562_);
v___x_577_ = lean_box(0);
v___y_489_ = v___y_561_;
v___y_490_ = v___y_560_;
v___y_491_ = v___y_563_;
v___y_492_ = v_terminationBy_x3f_564_;
v_partialFixpoint_x3f_493_ = v___x_577_;
v___y_494_ = v___y_565_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
goto v___jp_488_;
}
else
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = l_Lean_Syntax_getArg(v_val_562_, v___y_563_);
v___x_579_ = l_Lean_Syntax_isNone(v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_578_);
v___x_581_ = l_Lean_Syntax_matchesNull(v___x_578_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec(v___x_578_);
lean_dec(v_val_562_);
v___x_582_ = lean_box(0);
v___y_489_ = v___y_561_;
v___y_490_ = v___y_560_;
v___y_491_ = v___y_563_;
v___y_492_ = v_terminationBy_x3f_564_;
v_partialFixpoint_x3f_493_ = v___x_582_;
v___y_494_ = v___y_565_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
goto v___jp_488_;
}
else
{
lean_object* v_term_x3f_583_; lean_object* v___x_584_; 
v_term_x3f_583_ = l_Lean_Syntax_getArg(v___x_578_, v___y_563_);
lean_dec(v___x_578_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_term_x3f_583_);
v___y_544_ = v___y_569_;
v___y_545_ = v___y_565_;
v___y_546_ = v_val_562_;
v___y_547_ = v___y_567_;
v___y_548_ = v___y_560_;
v___y_549_ = v___y_561_;
v___y_550_ = v___y_570_;
v___y_551_ = v___y_563_;
v___y_552_ = v___y_568_;
v___y_553_ = v_terminationBy_x3f_564_;
v___y_554_ = v___y_566_;
v_term_x3f_555_ = v___x_584_;
goto v___jp_543_;
}
}
else
{
lean_object* v___x_585_; 
lean_dec(v___x_578_);
v___x_585_ = lean_box(0);
v___y_544_ = v___y_569_;
v___y_545_ = v___y_565_;
v___y_546_ = v_val_562_;
v___y_547_ = v___y_567_;
v___y_548_ = v___y_560_;
v___y_549_ = v___y_561_;
v___y_550_ = v___y_570_;
v___y_551_ = v___y_563_;
v___y_552_ = v___y_568_;
v___y_553_ = v_terminationBy_x3f_564_;
v___y_554_ = v___y_566_;
v_term_x3f_555_ = v___x_585_;
goto v___jp_543_;
}
}
}
else
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = l_Lean_Syntax_getArg(v_val_562_, v___y_563_);
v___x_587_ = l_Lean_Syntax_isNone(v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_586_);
v___x_589_ = l_Lean_Syntax_matchesNull(v___x_586_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_dec(v___x_586_);
lean_dec(v_val_562_);
v___x_590_ = lean_box(0);
v___y_489_ = v___y_561_;
v___y_490_ = v___y_560_;
v___y_491_ = v___y_563_;
v___y_492_ = v_terminationBy_x3f_564_;
v_partialFixpoint_x3f_493_ = v___x_590_;
v___y_494_ = v___y_565_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
goto v___jp_488_;
}
else
{
lean_object* v_term_x3f_591_; lean_object* v___x_592_; 
v_term_x3f_591_ = l_Lean_Syntax_getArg(v___x_586_, v___y_563_);
lean_dec(v___x_586_);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_term_x3f_591_);
v___y_528_ = v___y_569_;
v___y_529_ = v___y_565_;
v___y_530_ = v_val_562_;
v___y_531_ = v___y_567_;
v___y_532_ = v___y_560_;
v___y_533_ = v___y_561_;
v___y_534_ = v___y_570_;
v___y_535_ = v___y_563_;
v___y_536_ = v___y_568_;
v___y_537_ = v_terminationBy_x3f_564_;
v___y_538_ = v___y_566_;
v_term_x3f_539_ = v___x_592_;
goto v___jp_527_;
}
}
else
{
lean_object* v___x_593_; 
lean_dec(v___x_586_);
v___x_593_ = lean_box(0);
v___y_528_ = v___y_569_;
v___y_529_ = v___y_565_;
v___y_530_ = v_val_562_;
v___y_531_ = v___y_567_;
v___y_532_ = v___y_560_;
v___y_533_ = v___y_561_;
v___y_534_ = v___y_570_;
v___y_535_ = v___y_563_;
v___y_536_ = v___y_568_;
v___y_537_ = v_terminationBy_x3f_564_;
v___y_538_ = v___y_566_;
v_term_x3f_539_ = v___x_593_;
goto v___jp_527_;
}
}
}
else
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = l_Lean_Syntax_getArg(v_val_562_, v___y_563_);
v___x_595_ = l_Lean_Syntax_isNone(v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_594_);
v___x_597_ = l_Lean_Syntax_matchesNull(v___x_594_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v___x_594_);
lean_dec(v_val_562_);
v___x_598_ = lean_box(0);
v___y_489_ = v___y_561_;
v___y_490_ = v___y_560_;
v___y_491_ = v___y_563_;
v___y_492_ = v_terminationBy_x3f_564_;
v_partialFixpoint_x3f_493_ = v___x_598_;
v___y_494_ = v___y_565_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
goto v___jp_488_;
}
else
{
lean_object* v_term_x3f_599_; lean_object* v___x_600_; 
v_term_x3f_599_ = l_Lean_Syntax_getArg(v___x_594_, v___y_563_);
lean_dec(v___x_594_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_term_x3f_599_);
v___y_512_ = v___y_569_;
v___y_513_ = v___y_565_;
v___y_514_ = v_val_562_;
v___y_515_ = v___y_567_;
v___y_516_ = v___y_560_;
v___y_517_ = v___y_561_;
v___y_518_ = v___y_570_;
v___y_519_ = v___y_563_;
v___y_520_ = v___y_568_;
v___y_521_ = v_terminationBy_x3f_564_;
v___y_522_ = v___y_566_;
v_term_x3f_523_ = v___x_600_;
goto v___jp_511_;
}
}
else
{
lean_object* v___x_601_; 
lean_dec(v___x_594_);
v___x_601_ = lean_box(0);
v___y_512_ = v___y_569_;
v___y_513_ = v___y_565_;
v___y_514_ = v_val_562_;
v___y_515_ = v___y_567_;
v___y_516_ = v___y_560_;
v___y_517_ = v___y_561_;
v___y_518_ = v___y_570_;
v___y_519_ = v___y_563_;
v___y_520_ = v___y_568_;
v___y_521_ = v_terminationBy_x3f_564_;
v___y_522_ = v___y_566_;
v_term_x3f_523_ = v___x_601_;
goto v___jp_511_;
}
}
}
v___jp_602_:
{
if (lean_obj_tag(v___y_605_) == 1)
{
lean_object* v_val_614_; 
v_val_614_ = lean_ctor_get(v___y_605_, 0);
lean_inc(v_val_614_);
lean_dec_ref_known(v___y_605_, 1);
v___y_560_ = v___y_603_;
v___y_561_ = v___y_604_;
v_val_562_ = v_val_614_;
v___y_563_ = v___y_606_;
v_terminationBy_x3f_564_ = v_terminationBy_x3f_607_;
v___y_565_ = v___y_608_;
v___y_566_ = v___y_609_;
v___y_567_ = v___y_610_;
v___y_568_ = v___y_611_;
v___y_569_ = v___y_612_;
v___y_570_ = v___y_613_;
goto v___jp_559_;
}
else
{
lean_object* v___x_615_; 
lean_dec(v___y_605_);
v___x_615_ = lean_box(0);
v___y_489_ = v___y_604_;
v___y_490_ = v___y_603_;
v___y_491_ = v___y_606_;
v___y_492_ = v_terminationBy_x3f_607_;
v_partialFixpoint_x3f_493_ = v___x_615_;
v___y_494_ = v___y_608_;
v___y_495_ = v___y_609_;
v___y_496_ = v___y_610_;
v___y_497_ = v___y_611_;
v___y_498_ = v___y_612_;
v___y_499_ = v___y_613_;
goto v___jp_488_;
}
}
v___jp_616_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__17));
v___x_632_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_632_, 0, v___y_624_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
lean_ctor_set(v___x_632_, 2, v___y_617_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3, v___y_630_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3 + 1, v___y_618_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___y_603_ = v___y_626_;
v___y_604_ = v___y_619_;
v___y_605_ = v___y_621_;
v___y_606_ = v___y_627_;
v_terminationBy_x3f_607_ = v___x_633_;
v___y_608_ = v___y_622_;
v___y_609_ = v___y_629_;
v___y_610_ = v___y_623_;
v___y_611_ = v___y_625_;
v___y_612_ = v___y_628_;
v___y_613_ = v___y_620_;
goto v___jp_602_;
}
v___jp_634_:
{
lean_object* v___x_645_; 
v___x_645_ = lean_box(0);
v___y_603_ = v___y_639_;
v___y_604_ = v___y_638_;
v___y_605_ = v___y_640_;
v___y_606_ = v___y_642_;
v_terminationBy_x3f_607_ = v___x_645_;
v___y_608_ = v___y_636_;
v___y_609_ = v___y_644_;
v___y_610_ = v___y_635_;
v___y_611_ = v___y_637_;
v___y_612_ = v___y_643_;
v___y_613_ = v___y_641_;
goto v___jp_602_;
}
v___jp_646_:
{
lean_object* v___x_657_; 
v___x_657_ = lean_box(0);
v___y_603_ = v___y_651_;
v___y_604_ = v___y_650_;
v___y_605_ = v___y_652_;
v___y_606_ = v___y_654_;
v_terminationBy_x3f_607_ = v___x_657_;
v___y_608_ = v___y_648_;
v___y_609_ = v___y_656_;
v___y_610_ = v___y_647_;
v___y_611_ = v___y_649_;
v___y_612_ = v___y_655_;
v___y_613_ = v___y_653_;
goto v___jp_602_;
}
v___jp_658_:
{
lean_object* v___x_669_; 
v___x_669_ = lean_box(0);
v___y_603_ = v___y_663_;
v___y_604_ = v___y_662_;
v___y_605_ = v___y_664_;
v___y_606_ = v___y_666_;
v_terminationBy_x3f_607_ = v___x_669_;
v___y_608_ = v___y_660_;
v___y_609_ = v___y_668_;
v___y_610_ = v___y_659_;
v___y_611_ = v___y_661_;
v___y_612_ = v___y_667_;
v___y_613_ = v___y_665_;
goto v___jp_602_;
}
v___jp_670_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_686_, 0, v___y_678_);
lean_ctor_set(v___x_686_, 1, v___y_672_);
lean_ctor_set(v___x_686_, 2, v___y_671_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*3, v___y_685_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*3 + 1, v___y_682_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___y_603_ = v___y_680_;
v___y_604_ = v___y_673_;
v___y_605_ = v___y_674_;
v___y_606_ = v___y_681_;
v_terminationBy_x3f_607_ = v___x_687_;
v___y_608_ = v___y_676_;
v___y_609_ = v___y_684_;
v___y_610_ = v___y_677_;
v___y_611_ = v___y_679_;
v___y_612_ = v___y_683_;
v___y_613_ = v___y_675_;
goto v___jp_602_;
}
v___jp_688_:
{
lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(2u);
v___x_702_ = l_Lean_Syntax_getArg(v___y_692_, v___x_701_);
lean_inc(v___x_702_);
v___x_703_ = l_Lean_Syntax_matchesNull(v___x_702_, v___x_701_);
if (v___x_703_ == 0)
{
uint8_t v___x_704_; 
v___x_704_ = l_Lean_Syntax_matchesNull(v___x_702_, v___x_457_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_s_700_);
lean_dec(v___y_695_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
lean_dec(v_stx_423_);
v___x_705_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_706_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___y_692_, v___x_705_, v___y_690_, v___y_699_, v___y_689_, v___y_691_, v___y_698_, v___y_696_);
lean_dec(v___y_692_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v___x_715_; lean_object* v_body_716_; 
v___x_715_ = lean_unsigned_to_nat(3u);
v_body_716_ = l_Lean_Syntax_getArg(v___y_692_, v___x_715_);
if (lean_obj_tag(v_s_700_) == 0)
{
v___y_617_ = v_body_716_;
v___y_618_ = v___x_703_;
v___y_619_ = v___y_693_;
v___y_620_ = v___y_696_;
v___y_621_ = v___y_695_;
v___y_622_ = v___y_690_;
v___y_623_ = v___y_689_;
v___y_624_ = v___y_692_;
v___y_625_ = v___y_691_;
v___y_626_ = v___y_694_;
v___y_627_ = v___y_697_;
v___y_628_ = v___y_698_;
v___y_629_ = v___y_699_;
v___y_630_ = v___x_703_;
goto v___jp_616_;
}
else
{
lean_dec_ref_known(v_s_700_, 1);
v___y_617_ = v_body_716_;
v___y_618_ = v___x_703_;
v___y_619_ = v___y_693_;
v___y_620_ = v___y_696_;
v___y_621_ = v___y_695_;
v___y_622_ = v___y_690_;
v___y_623_ = v___y_689_;
v___y_624_ = v___y_692_;
v___y_625_ = v___y_691_;
v___y_626_ = v___y_694_;
v___y_627_ = v___y_697_;
v___y_628_ = v___y_698_;
v___y_629_ = v___y_699_;
v___y_630_ = v___x_704_;
goto v___jp_616_;
}
}
}
else
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = l_Lean_Syntax_getArg(v___x_702_, v___x_457_);
lean_dec(v___x_702_);
lean_inc(v___x_717_);
v___x_718_ = l_Lean_Syntax_matchesNull(v___x_717_, v___x_457_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v_body_720_; lean_object* v_vars_721_; 
v___x_719_ = lean_unsigned_to_nat(3u);
v_body_720_ = l_Lean_Syntax_getArg(v___y_692_, v___x_719_);
v_vars_721_ = l_Lean_Syntax_getArgs(v___x_717_);
lean_dec(v___x_717_);
if (lean_obj_tag(v_s_700_) == 0)
{
v___y_671_ = v_body_720_;
v___y_672_ = v_vars_721_;
v___y_673_ = v___y_693_;
v___y_674_ = v___y_695_;
v___y_675_ = v___y_696_;
v___y_676_ = v___y_690_;
v___y_677_ = v___y_689_;
v___y_678_ = v___y_692_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_694_;
v___y_681_ = v___y_697_;
v___y_682_ = v___x_718_;
v___y_683_ = v___y_698_;
v___y_684_ = v___y_699_;
v___y_685_ = v___x_718_;
goto v___jp_670_;
}
else
{
lean_dec_ref_known(v_s_700_, 1);
v___y_671_ = v_body_720_;
v___y_672_ = v_vars_721_;
v___y_673_ = v___y_693_;
v___y_674_ = v___y_695_;
v___y_675_ = v___y_696_;
v___y_676_ = v___y_690_;
v___y_677_ = v___y_689_;
v___y_678_ = v___y_692_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_694_;
v___y_681_ = v___y_697_;
v___y_682_ = v___x_718_;
v___y_683_ = v___y_698_;
v___y_684_ = v___y_699_;
v___y_685_ = v___x_703_;
goto v___jp_670_;
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v___x_717_);
lean_dec(v_s_700_);
lean_dec(v___y_695_);
lean_dec(v___y_694_);
lean_dec(v___y_693_);
lean_dec(v_stx_423_);
v___x_722_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21);
v___x_723_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___y_692_, v___x_722_, v___y_690_, v___y_699_, v___y_689_, v___y_691_, v___y_698_, v___y_696_);
lean_dec(v___y_692_);
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
v___jp_732_:
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23));
lean_inc(v_val_735_);
v___x_745_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25));
lean_inc(v_val_735_);
v___x_747_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12));
lean_inc(v_val_735_);
v___x_749_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14));
lean_inc(v_val_735_);
v___x_751_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16));
lean_inc(v_val_735_);
v___x_753_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_terminationBy_x3f_x3f_737_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v_stx_423_);
v___x_754_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_755_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_754_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v_val_735_);
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
else
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = l_Lean_Syntax_getArg(v_val_735_, v___y_736_);
v___x_765_ = l_Lean_Syntax_isNone(v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = lean_unsigned_to_nat(2u);
v___x_767_ = l_Lean_Syntax_matchesNull(v___x_764_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_terminationBy_x3f_x3f_737_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v_stx_423_);
v___x_768_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_769_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_768_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v_val_735_);
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_dec(v_val_735_);
v___y_659_ = v___y_740_;
v___y_660_ = v___y_738_;
v___y_661_ = v___y_741_;
v___y_662_ = v_terminationBy_x3f_x3f_737_;
v___y_663_ = v___y_733_;
v___y_664_ = v___y_734_;
v___y_665_ = v___y_743_;
v___y_666_ = v___y_736_;
v___y_667_ = v___y_742_;
v___y_668_ = v___y_739_;
goto v___jp_658_;
}
}
else
{
lean_dec(v___x_764_);
lean_dec(v_val_735_);
v___y_659_ = v___y_740_;
v___y_660_ = v___y_738_;
v___y_661_ = v___y_741_;
v___y_662_ = v_terminationBy_x3f_x3f_737_;
v___y_663_ = v___y_733_;
v___y_664_ = v___y_734_;
v___y_665_ = v___y_743_;
v___y_666_ = v___y_736_;
v___y_667_ = v___y_742_;
v___y_668_ = v___y_739_;
goto v___jp_658_;
}
}
}
else
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = l_Lean_Syntax_getArg(v_val_735_, v___y_736_);
v___x_779_ = l_Lean_Syntax_isNone(v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(2u);
v___x_781_ = l_Lean_Syntax_matchesNull(v___x_778_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_terminationBy_x3f_x3f_737_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v_stx_423_);
v___x_782_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_783_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_782_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v_val_735_);
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_dec(v_val_735_);
v___y_647_ = v___y_740_;
v___y_648_ = v___y_738_;
v___y_649_ = v___y_741_;
v___y_650_ = v_terminationBy_x3f_x3f_737_;
v___y_651_ = v___y_733_;
v___y_652_ = v___y_734_;
v___y_653_ = v___y_743_;
v___y_654_ = v___y_736_;
v___y_655_ = v___y_742_;
v___y_656_ = v___y_739_;
goto v___jp_646_;
}
}
else
{
lean_dec(v___x_778_);
lean_dec(v_val_735_);
v___y_647_ = v___y_740_;
v___y_648_ = v___y_738_;
v___y_649_ = v___y_741_;
v___y_650_ = v_terminationBy_x3f_x3f_737_;
v___y_651_ = v___y_733_;
v___y_652_ = v___y_734_;
v___y_653_ = v___y_743_;
v___y_654_ = v___y_736_;
v___y_655_ = v___y_742_;
v___y_656_ = v___y_739_;
goto v___jp_646_;
}
}
}
else
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = l_Lean_Syntax_getArg(v_val_735_, v___y_736_);
v___x_793_ = l_Lean_Syntax_isNone(v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(2u);
v___x_795_ = l_Lean_Syntax_matchesNull(v___x_792_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v_terminationBy_x3f_x3f_737_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v_stx_423_);
v___x_796_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_797_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_796_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v_val_735_);
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
else
{
lean_dec(v_val_735_);
v___y_635_ = v___y_740_;
v___y_636_ = v___y_738_;
v___y_637_ = v___y_741_;
v___y_638_ = v_terminationBy_x3f_x3f_737_;
v___y_639_ = v___y_733_;
v___y_640_ = v___y_734_;
v___y_641_ = v___y_743_;
v___y_642_ = v___y_736_;
v___y_643_ = v___y_742_;
v___y_644_ = v___y_739_;
goto v___jp_634_;
}
}
else
{
lean_dec(v___x_792_);
lean_dec(v_val_735_);
v___y_635_ = v___y_740_;
v___y_636_ = v___y_738_;
v___y_637_ = v___y_741_;
v___y_638_ = v_terminationBy_x3f_x3f_737_;
v___y_639_ = v___y_733_;
v___y_640_ = v___y_734_;
v___y_641_ = v___y_743_;
v___y_642_ = v___y_736_;
v___y_643_ = v___y_742_;
v___y_644_ = v___y_739_;
goto v___jp_634_;
}
}
}
else
{
lean_object* v___x_806_; 
lean_dec(v___y_734_);
v___x_806_ = lean_box(0);
v___y_560_ = v___y_733_;
v___y_561_ = v_terminationBy_x3f_x3f_737_;
v_val_562_ = v_val_735_;
v___y_563_ = v___y_736_;
v_terminationBy_x3f_564_ = v___x_806_;
v___y_565_ = v___y_738_;
v___y_566_ = v___y_739_;
v___y_567_ = v___y_740_;
v___y_568_ = v___y_741_;
v___y_569_ = v___y_742_;
v___y_570_ = v___y_743_;
goto v___jp_559_;
}
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = l_Lean_Syntax_getArg(v_val_735_, v___y_736_);
v___x_808_ = l_Lean_Syntax_isNone(v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; 
lean_inc(v___x_807_);
v___x_809_ = l_Lean_Syntax_matchesNull(v___x_807_, v___y_736_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___x_807_);
lean_dec(v_terminationBy_x3f_x3f_737_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v_stx_423_);
v___x_810_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_811_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_810_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v_val_735_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v_s_820_; lean_object* v___x_821_; 
v_s_820_ = l_Lean_Syntax_getArg(v___x_807_, v___x_457_);
lean_dec(v___x_807_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v_s_820_);
v___y_689_ = v___y_740_;
v___y_690_ = v___y_738_;
v___y_691_ = v___y_741_;
v___y_692_ = v_val_735_;
v___y_693_ = v_terminationBy_x3f_x3f_737_;
v___y_694_ = v___y_733_;
v___y_695_ = v___y_734_;
v___y_696_ = v___y_743_;
v___y_697_ = v___y_736_;
v___y_698_ = v___y_742_;
v___y_699_ = v___y_739_;
v_s_700_ = v___x_821_;
goto v___jp_688_;
}
}
else
{
lean_object* v___x_822_; 
lean_dec(v___x_807_);
v___x_822_ = lean_box(0);
v___y_689_ = v___y_740_;
v___y_690_ = v___y_738_;
v___y_691_ = v___y_741_;
v___y_692_ = v_val_735_;
v___y_693_ = v_terminationBy_x3f_x3f_737_;
v___y_694_ = v___y_733_;
v___y_695_ = v___y_734_;
v___y_696_ = v___y_743_;
v___y_697_ = v___y_736_;
v___y_698_ = v___y_742_;
v___y_699_ = v___y_739_;
v_s_700_ = v___x_822_;
goto v___jp_688_;
}
}
}
v___jp_823_:
{
if (lean_obj_tag(v___y_824_) == 1)
{
lean_object* v_val_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_val_827_ = lean_ctor_get(v___y_824_, 0);
lean_inc_n(v_val_827_, 2);
v___x_828_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25));
v___x_829_ = l_Lean_Syntax_isOfKind(v_val_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
v___x_830_ = lean_box(0);
v___y_733_ = v_d_x3f_826_;
v___y_734_ = v___y_824_;
v_val_735_ = v_val_827_;
v___y_736_ = v___y_825_;
v_terminationBy_x3f_x3f_737_ = v___x_830_;
v___y_738_ = v___y_424_;
v___y_739_ = v___y_425_;
v___y_740_ = v___y_426_;
v___y_741_ = v___y_427_;
v___y_742_ = v___y_428_;
v___y_743_ = v___y_429_;
goto v___jp_732_;
}
else
{
lean_object* v___x_831_; 
lean_inc(v_val_827_);
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v_val_827_);
v___y_733_ = v_d_x3f_826_;
v___y_734_ = v___y_824_;
v_val_735_ = v_val_827_;
v___y_736_ = v___y_825_;
v_terminationBy_x3f_x3f_737_ = v___x_831_;
v___y_738_ = v___y_424_;
v___y_739_ = v___y_425_;
v___y_740_ = v___y_426_;
v___y_741_ = v___y_427_;
v___y_742_ = v___y_428_;
v___y_743_ = v___y_429_;
goto v___jp_732_;
}
}
else
{
lean_object* v___x_832_; 
v___x_832_ = lean_box(0);
if (lean_obj_tag(v___y_824_) == 1)
{
lean_object* v_val_833_; 
v_val_833_ = lean_ctor_get(v___y_824_, 0);
lean_inc(v_val_833_);
v___y_733_ = v_d_x3f_826_;
v___y_734_ = v___y_824_;
v_val_735_ = v_val_833_;
v___y_736_ = v___y_825_;
v_terminationBy_x3f_x3f_737_ = v___x_832_;
v___y_738_ = v___y_424_;
v___y_739_ = v___y_425_;
v___y_740_ = v___y_426_;
v___y_741_ = v___y_427_;
v___y_742_ = v___y_428_;
v___y_743_ = v___y_429_;
goto v___jp_732_;
}
else
{
v___y_603_ = v_d_x3f_826_;
v___y_604_ = v___x_832_;
v___y_605_ = v___y_824_;
v___y_606_ = v___y_825_;
v_terminationBy_x3f_607_ = v___x_832_;
v___y_608_ = v___y_424_;
v___y_609_ = v___y_425_;
v___y_610_ = v___y_426_;
v___y_611_ = v___y_427_;
v___y_612_ = v___y_428_;
v___y_613_ = v___y_429_;
goto v___jp_602_;
}
}
}
v___jp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = l_Lean_Syntax_getArg(v_stx_423_, v___x_836_);
v___x_838_ = l_Lean_Syntax_isNone(v___x_837_);
if (v___x_838_ == 0)
{
uint8_t v___x_839_; 
lean_inc(v___x_837_);
v___x_839_ = l_Lean_Syntax_matchesNull(v___x_837_, v___x_836_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v___x_837_);
lean_dec(v_t_x3f_835_);
v___x_840_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_841_ = lean_box(0);
lean_inc_n(v_stx_423_, 2);
v___x_842_ = l_Lean_Syntax_formatStx(v_stx_423_, v___x_841_, v___x_839_);
v___x_843_ = l_Std_Format_defWidth;
v___x_844_ = l_Std_Format_pretty(v___x_842_, v___x_843_, v___x_457_, v___x_457_);
v___x_845_ = lean_string_append(v___x_840_, v___x_844_);
lean_dec_ref(v___x_844_);
v___x_846_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_847_ = lean_string_append(v___x_845_, v___x_846_);
v___x_848_ = l_Lean_Syntax_getKind(v_stx_423_);
v___x_849_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_848_, v___x_440_);
v___x_850_ = lean_string_append(v___x_847_, v___x_849_);
lean_dec_ref(v___x_849_);
v___x_851_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
v___x_852_ = l_Lean_MessageData_ofFormat(v___x_851_);
v___x_853_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_423_, v___x_852_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v_stx_423_);
return v___x_853_;
}
else
{
lean_object* v_d_x3f_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_d_x3f_854_ = l_Lean_Syntax_getArg(v___x_837_, v___x_457_);
lean_dec(v___x_837_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8));
lean_inc(v_d_x3f_854_);
v___x_856_ = l_Lean_Syntax_isOfKind(v_d_x3f_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_dec(v_d_x3f_854_);
lean_dec(v_t_x3f_835_);
v___x_857_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_858_ = lean_box(0);
lean_inc_n(v_stx_423_, 2);
v___x_859_ = l_Lean_Syntax_formatStx(v_stx_423_, v___x_858_, v___x_856_);
v___x_860_ = l_Std_Format_defWidth;
v___x_861_ = l_Std_Format_pretty(v___x_859_, v___x_860_, v___x_457_, v___x_457_);
v___x_862_ = lean_string_append(v___x_857_, v___x_861_);
lean_dec_ref(v___x_861_);
v___x_863_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_864_ = lean_string_append(v___x_862_, v___x_863_);
v___x_865_ = l_Lean_Syntax_getKind(v_stx_423_);
v___x_866_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_865_, v___x_839_);
v___x_867_ = lean_string_append(v___x_864_, v___x_866_);
lean_dec_ref(v___x_866_);
v___x_868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
v___x_869_ = l_Lean_MessageData_ofFormat(v___x_868_);
v___x_870_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_423_, v___x_869_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v_stx_423_);
return v___x_870_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v_d_x3f_854_);
v___y_824_ = v_t_x3f_835_;
v___y_825_ = v___x_836_;
v_d_x3f_826_ = v___x_871_;
goto v___jp_823_;
}
}
}
else
{
lean_object* v___x_872_; 
lean_dec(v___x_837_);
v___x_872_ = lean_box(0);
v___y_824_ = v_t_x3f_835_;
v___y_825_ = v___x_836_;
v_d_x3f_826_ = v___x_872_;
goto v___jp_823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___boxed(lean_object* v_stx_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(v_stx_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_902_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0(uint8_t v___y_911_, uint8_t v_suppressElabErrors_912_, lean_object* v_x_913_){
_start:
{
if (lean_obj_tag(v_x_913_) == 1)
{
lean_object* v_pre_914_; 
v_pre_914_ = lean_ctor_get(v_x_913_, 0);
switch(lean_obj_tag(v_pre_914_))
{
case 1:
{
lean_object* v_pre_915_; 
v_pre_915_ = lean_ctor_get(v_pre_914_, 0);
switch(lean_obj_tag(v_pre_915_))
{
case 0:
{
lean_object* v_str_916_; lean_object* v_str_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_str_916_ = lean_ctor_get(v_x_913_, 1);
v_str_917_ = lean_ctor_get(v_pre_914_, 1);
v___x_918_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__0));
v___x_919_ = lean_string_dec_eq(v_str_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__1));
v___x_921_ = lean_string_dec_eq(v_str_917_, v___x_920_);
if (v___x_921_ == 0)
{
return v___y_911_;
}
else
{
lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__2));
v___x_923_ = lean_string_dec_eq(v_str_916_, v___x_922_);
if (v___x_923_ == 0)
{
return v___y_911_;
}
else
{
return v_suppressElabErrors_912_;
}
}
}
else
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__3));
v___x_925_ = lean_string_dec_eq(v_str_916_, v___x_924_);
if (v___x_925_ == 0)
{
return v___y_911_;
}
else
{
return v_suppressElabErrors_912_;
}
}
}
case 1:
{
lean_object* v_pre_926_; 
v_pre_926_ = lean_ctor_get(v_pre_915_, 0);
if (lean_obj_tag(v_pre_926_) == 0)
{
lean_object* v_str_927_; lean_object* v_str_928_; lean_object* v_str_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_str_927_ = lean_ctor_get(v_x_913_, 1);
v_str_928_ = lean_ctor_get(v_pre_914_, 1);
v_str_929_ = lean_ctor_get(v_pre_915_, 1);
v___x_930_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__4));
v___x_931_ = lean_string_dec_eq(v_str_929_, v___x_930_);
if (v___x_931_ == 0)
{
return v___y_911_;
}
else
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__5));
v___x_933_ = lean_string_dec_eq(v_str_928_, v___x_932_);
if (v___x_933_ == 0)
{
return v___y_911_;
}
else
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__6));
v___x_935_ = lean_string_dec_eq(v_str_927_, v___x_934_);
if (v___x_935_ == 0)
{
return v___y_911_;
}
else
{
return v_suppressElabErrors_912_;
}
}
}
}
else
{
return v___y_911_;
}
}
default: 
{
return v___y_911_;
}
}
}
case 0:
{
lean_object* v_str_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_str_936_ = lean_ctor_get(v_x_913_, 1);
v___x_937_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__7));
v___x_938_ = lean_string_dec_eq(v_str_936_, v___x_937_);
if (v___x_938_ == 0)
{
return v___y_911_;
}
else
{
return v_suppressElabErrors_912_;
}
}
default: 
{
return v___y_911_;
}
}
}
else
{
return v___y_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___boxed(lean_object* v___y_939_, lean_object* v_suppressElabErrors_940_, lean_object* v_x_941_){
_start:
{
uint8_t v___y_53600__boxed_942_; uint8_t v_suppressElabErrors_boxed_943_; uint8_t v_res_944_; lean_object* v_r_945_; 
v___y_53600__boxed_942_ = lean_unbox(v___y_939_);
v_suppressElabErrors_boxed_943_ = lean_unbox(v_suppressElabErrors_940_);
v_res_944_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0(v___y_53600__boxed_942_, v_suppressElabErrors_boxed_943_, v_x_941_);
lean_dec(v_x_941_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(lean_object* v_ref_947_, lean_object* v_msgData_948_, uint8_t v_severity_949_, uint8_t v_isSilent_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
uint8_t v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; uint8_t v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_993_; uint8_t v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; uint8_t v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1018_; uint8_t v___y_1019_; uint8_t v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; uint8_t v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1029_; uint8_t v___y_1030_; uint8_t v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; uint8_t v___y_1035_; uint8_t v___x_1040_; uint8_t v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; uint8_t v___y_1047_; uint8_t v___y_1048_; uint8_t v___y_1050_; uint8_t v___x_1065_; 
v___x_1040_ = 2;
v___x_1065_ = l_Lean_instBEqMessageSeverity_beq(v_severity_949_, v___x_1040_);
if (v___x_1065_ == 0)
{
v___y_1050_ = v___x_1065_;
goto v___jp_1049_;
}
else
{
uint8_t v___x_1066_; 
lean_inc_ref(v_msgData_948_);
v___x_1066_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_948_);
v___y_1050_ = v___x_1066_;
goto v___jp_1049_;
}
v___jp_956_:
{
lean_object* v___x_966_; lean_object* v_currNamespace_967_; lean_object* v_openDecls_968_; lean_object* v_env_969_; lean_object* v_nextMacroScope_970_; lean_object* v_ngen_971_; lean_object* v_auxDeclNGen_972_; lean_object* v_traceState_973_; lean_object* v_cache_974_; lean_object* v_messages_975_; lean_object* v_infoState_976_; lean_object* v_snapshotTasks_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_991_; 
v___x_966_ = lean_st_ref_take(v___y_965_);
v_currNamespace_967_ = lean_ctor_get(v___y_964_, 6);
v_openDecls_968_ = lean_ctor_get(v___y_964_, 7);
v_env_969_ = lean_ctor_get(v___x_966_, 0);
v_nextMacroScope_970_ = lean_ctor_get(v___x_966_, 1);
v_ngen_971_ = lean_ctor_get(v___x_966_, 2);
v_auxDeclNGen_972_ = lean_ctor_get(v___x_966_, 3);
v_traceState_973_ = lean_ctor_get(v___x_966_, 4);
v_cache_974_ = lean_ctor_get(v___x_966_, 5);
v_messages_975_ = lean_ctor_get(v___x_966_, 6);
v_infoState_976_ = lean_ctor_get(v___x_966_, 7);
v_snapshotTasks_977_ = lean_ctor_get(v___x_966_, 8);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_991_ == 0)
{
v___x_979_ = v___x_966_;
v_isShared_980_ = v_isSharedCheck_991_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snapshotTasks_977_);
lean_inc(v_infoState_976_);
lean_inc(v_messages_975_);
lean_inc(v_cache_974_);
lean_inc(v_traceState_973_);
lean_inc(v_auxDeclNGen_972_);
lean_inc(v_ngen_971_);
lean_inc(v_nextMacroScope_970_);
lean_inc(v_env_969_);
lean_dec(v___x_966_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_991_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
lean_inc(v_openDecls_968_);
lean_inc(v_currNamespace_967_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v_currNamespace_967_);
lean_ctor_set(v___x_981_, 1, v_openDecls_968_);
v___x_982_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___y_962_);
lean_inc_ref(v___y_961_);
lean_inc_ref(v___y_963_);
v___x_983_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_983_, 0, v___y_963_);
lean_ctor_set(v___x_983_, 1, v___y_958_);
lean_ctor_set(v___x_983_, 2, v___y_959_);
lean_ctor_set(v___x_983_, 3, v___y_961_);
lean_ctor_set(v___x_983_, 4, v___x_982_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*5, v___y_957_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*5 + 1, v___y_960_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*5 + 2, v_isSilent_950_);
v___x_984_ = l_Lean_MessageLog_add(v___x_983_, v_messages_975_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 6, v___x_984_);
v___x_986_ = v___x_979_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_env_969_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_nextMacroScope_970_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_ngen_971_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v_auxDeclNGen_972_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_traceState_973_);
lean_ctor_set(v_reuseFailAlloc_990_, 5, v_cache_974_);
lean_ctor_set(v_reuseFailAlloc_990_, 6, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_990_, 7, v_infoState_976_);
lean_ctor_set(v_reuseFailAlloc_990_, 8, v_snapshotTasks_977_);
v___x_986_ = v_reuseFailAlloc_990_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_st_ref_set(v___y_965_, v___x_986_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
}
v___jp_992_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1016_; 
v___x_1001_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_948_);
v___x_1002_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16(v___x_1001_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1016_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1016_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_inc_ref_n(v___y_996_, 2);
v___x_1007_ = l_Lean_FileMap_toPosition(v___y_996_, v___y_998_);
lean_dec(v___y_998_);
v___x_1008_ = l_Lean_FileMap_toPosition(v___y_996_, v___y_1000_);
lean_dec(v___y_1000_);
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0));
if (v___y_994_ == 0)
{
lean_del_object(v___x_1005_);
lean_dec_ref(v___y_993_);
v___y_957_ = v___y_995_;
v___y_958_ = v___x_1007_;
v___y_959_ = v___x_1009_;
v___y_960_ = v___y_997_;
v___y_961_ = v___x_1010_;
v___y_962_ = v_a_1003_;
v___y_963_ = v___y_999_;
v___y_964_ = v___y_953_;
v___y_965_ = v___y_954_;
goto v___jp_956_;
}
else
{
uint8_t v___x_1011_; 
lean_inc(v_a_1003_);
v___x_1011_ = l_Lean_MessageData_hasTag(v___y_993_, v_a_1003_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
lean_dec_ref_known(v___x_1009_, 1);
lean_dec_ref(v___x_1007_);
lean_dec(v_a_1003_);
v___x_1012_ = lean_box(0);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1012_);
v___x_1014_ = v___x_1005_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_del_object(v___x_1005_);
v___y_957_ = v___y_995_;
v___y_958_ = v___x_1007_;
v___y_959_ = v___x_1009_;
v___y_960_ = v___y_997_;
v___y_961_ = v___x_1010_;
v___y_962_ = v_a_1003_;
v___y_963_ = v___y_999_;
v___y_964_ = v___y_953_;
v___y_965_ = v___y_954_;
goto v___jp_956_;
}
}
}
}
v___jp_1017_:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_Syntax_getTailPos_x3f(v___y_1021_, v___y_1020_);
lean_dec(v___y_1021_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_inc(v___y_1025_);
v___y_993_ = v___y_1018_;
v___y_994_ = v___y_1019_;
v___y_995_ = v___y_1020_;
v___y_996_ = v___y_1022_;
v___y_997_ = v___y_1023_;
v___y_998_ = v___y_1025_;
v___y_999_ = v___y_1024_;
v___y_1000_ = v___y_1025_;
goto v___jp_992_;
}
else
{
lean_object* v_val_1027_; 
v_val_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_val_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___y_993_ = v___y_1018_;
v___y_994_ = v___y_1019_;
v___y_995_ = v___y_1020_;
v___y_996_ = v___y_1022_;
v___y_997_ = v___y_1023_;
v___y_998_ = v___y_1025_;
v___y_999_ = v___y_1024_;
v___y_1000_ = v_val_1027_;
goto v___jp_992_;
}
}
v___jp_1028_:
{
lean_object* v_ref_1036_; lean_object* v___x_1037_; 
v_ref_1036_ = l_Lean_replaceRef(v_ref_947_, v___y_1032_);
v___x_1037_ = l_Lean_Syntax_getPos_x3f(v_ref_1036_, v___y_1031_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_unsigned_to_nat(0u);
v___y_1018_ = v___y_1029_;
v___y_1019_ = v___y_1030_;
v___y_1020_ = v___y_1031_;
v___y_1021_ = v_ref_1036_;
v___y_1022_ = v___y_1033_;
v___y_1023_ = v___y_1035_;
v___y_1024_ = v___y_1034_;
v___y_1025_ = v___x_1038_;
goto v___jp_1017_;
}
else
{
lean_object* v_val_1039_; 
v_val_1039_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1039_);
lean_dec_ref_known(v___x_1037_, 1);
v___y_1018_ = v___y_1029_;
v___y_1019_ = v___y_1030_;
v___y_1020_ = v___y_1031_;
v___y_1021_ = v_ref_1036_;
v___y_1022_ = v___y_1033_;
v___y_1023_ = v___y_1035_;
v___y_1024_ = v___y_1034_;
v___y_1025_ = v_val_1039_;
goto v___jp_1017_;
}
}
v___jp_1041_:
{
if (v___y_1048_ == 0)
{
v___y_1029_ = v___y_1043_;
v___y_1030_ = v___y_1042_;
v___y_1031_ = v___y_1047_;
v___y_1032_ = v___y_1044_;
v___y_1033_ = v___y_1045_;
v___y_1034_ = v___y_1046_;
v___y_1035_ = v_severity_949_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v___y_1043_;
v___y_1030_ = v___y_1042_;
v___y_1031_ = v___y_1047_;
v___y_1032_ = v___y_1044_;
v___y_1033_ = v___y_1045_;
v___y_1034_ = v___y_1046_;
v___y_1035_ = v___x_1040_;
goto v___jp_1028_;
}
}
v___jp_1049_:
{
if (v___y_1050_ == 0)
{
lean_object* v_fileName_1051_; lean_object* v_fileMap_1052_; lean_object* v_options_1053_; lean_object* v_ref_1054_; uint8_t v_suppressElabErrors_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; uint8_t v___x_1059_; uint8_t v___x_1060_; 
v_fileName_1051_ = lean_ctor_get(v___y_953_, 0);
v_fileMap_1052_ = lean_ctor_get(v___y_953_, 1);
v_options_1053_ = lean_ctor_get(v___y_953_, 2);
v_ref_1054_ = lean_ctor_get(v___y_953_, 5);
v_suppressElabErrors_1055_ = lean_ctor_get_uint8(v___y_953_, sizeof(void*)*14 + 1);
v___x_1056_ = lean_box(v___y_1050_);
v___x_1057_ = lean_box(v_suppressElabErrors_1055_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1058_, 0, v___x_1056_);
lean_closure_set(v___f_1058_, 1, v___x_1057_);
v___x_1059_ = 1;
v___x_1060_ = l_Lean_instBEqMessageSeverity_beq(v_severity_949_, v___x_1059_);
if (v___x_1060_ == 0)
{
v___y_1042_ = v_suppressElabErrors_1055_;
v___y_1043_ = v___f_1058_;
v___y_1044_ = v_ref_1054_;
v___y_1045_ = v_fileMap_1052_;
v___y_1046_ = v_fileName_1051_;
v___y_1047_ = v___y_1050_;
v___y_1048_ = v___x_1060_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = l_Lean_warningAsError;
v___x_1062_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_options_1053_, v___x_1061_);
v___y_1042_ = v_suppressElabErrors_1055_;
v___y_1043_ = v___f_1058_;
v___y_1044_ = v_ref_1054_;
v___y_1045_ = v_fileMap_1052_;
v___y_1046_ = v_fileName_1051_;
v___y_1047_ = v___y_1050_;
v___y_1048_ = v___x_1062_;
goto v___jp_1041_;
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec_ref(v_msgData_948_);
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___boxed(lean_object* v_ref_1067_, lean_object* v_msgData_1068_, lean_object* v_severity_1069_, lean_object* v_isSilent_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
uint8_t v_severity_boxed_1076_; uint8_t v_isSilent_boxed_1077_; lean_object* v_res_1078_; 
v_severity_boxed_1076_ = lean_unbox(v_severity_1069_);
v_isSilent_boxed_1077_ = lean_unbox(v_isSilent_1070_);
v_res_1078_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(v_ref_1067_, v_msgData_1068_, v_severity_boxed_1076_, v_isSilent_boxed_1077_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_ref_1067_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44(lean_object* v_msgData_1079_, uint8_t v_severity_1080_, uint8_t v_isSilent_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_ref_1089_; lean_object* v___x_1090_; 
v_ref_1089_ = lean_ctor_get(v___y_1086_, 5);
v___x_1090_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(v_ref_1089_, v_msgData_1079_, v_severity_1080_, v_isSilent_1081_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44___boxed(lean_object* v_msgData_1091_, lean_object* v_severity_1092_, lean_object* v_isSilent_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
uint8_t v_severity_boxed_1101_; uint8_t v_isSilent_boxed_1102_; lean_object* v_res_1103_; 
v_severity_boxed_1101_ = lean_unbox(v_severity_1092_);
v_isSilent_boxed_1102_ = lean_unbox(v_isSilent_1093_);
v_res_1103_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44(v_msgData_1091_, v_severity_boxed_1101_, v_isSilent_boxed_1102_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39(lean_object* v_msgData_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
uint8_t v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = 2;
v___x_1113_ = 0;
v___x_1114_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44(v_msgData_1104_, v___x_1112_, v___x_1113_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39___boxed(lean_object* v_msgData_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39(v_msgData_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38(lean_object* v_ref_1124_, lean_object* v_msgData_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = 2;
v___x_1134_ = 0;
v___x_1135_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(v_ref_1124_, v_msgData_1125_, v___x_1133_, v___x_1134_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38___boxed(lean_object* v_ref_1136_, lean_object* v_msgData_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38(v_ref_1136_, v_msgData_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v_ref_1136_);
return v_res_1145_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__0));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32(lean_object* v_ex_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
if (lean_obj_tag(v_ex_1149_) == 0)
{
lean_object* v_ref_1157_; lean_object* v_msg_1158_; lean_object* v___x_1159_; 
v_ref_1157_ = lean_ctor_get(v_ex_1149_, 0);
lean_inc(v_ref_1157_);
v_msg_1158_ = lean_ctor_get(v_ex_1149_, 1);
lean_inc_ref(v_msg_1158_);
lean_dec_ref_known(v_ex_1149_, 2);
v___x_1159_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38(v_ref_1157_, v_msg_1158_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v_ref_1157_);
return v___x_1159_;
}
else
{
lean_object* v_id_1160_; uint8_t v___y_1162_; uint8_t v___x_1184_; 
v_id_1160_ = lean_ctor_get(v_ex_1149_, 0);
lean_inc(v_id_1160_);
v___x_1184_ = l_Lean_Elab_isAbortExceptionId(v_id_1160_);
if (v___x_1184_ == 0)
{
uint8_t v___x_1185_; 
v___x_1185_ = l_Lean_Exception_isInterrupt(v_ex_1149_);
lean_dec_ref_known(v_ex_1149_, 2);
v___y_1162_ = v___x_1185_;
goto v___jp_1161_;
}
else
{
lean_dec_ref_known(v_ex_1149_, 2);
v___y_1162_ = v___x_1184_;
goto v___jp_1161_;
}
v___jp_1161_:
{
if (v___y_1162_ == 0)
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_InternalExceptionId_getName(v_id_1160_);
lean_dec(v_id_1160_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
v___x_1165_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1);
v___x_1166_ = l_Lean_MessageData_ofName(v_a_1164_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39(v___x_1167_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1181_; 
v_a_1169_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1171_ = v___x_1163_;
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1163_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1181_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_ref_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v_ref_1173_ = lean_ctor_get(v___y_1154_, 5);
v___x_1174_ = lean_io_error_to_string(v_a_1169_);
v___x_1175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
v___x_1176_ = l_Lean_MessageData_ofFormat(v___x_1175_);
lean_inc(v_ref_1173_);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_ref_1173_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1177_);
v___x_1179_ = v___x_1171_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec(v_id_1160_);
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___boxed(lean_object* v_ex_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32(v_ex_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0(lean_object* v_k_1202_){
_start:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2));
v___x_1204_ = lean_name_eq(v_k_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
uint8_t v___x_1205_; 
v___x_1205_ = 1;
return v___x_1205_;
}
else
{
uint8_t v___x_1206_; 
v___x_1206_ = 0;
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___boxed(lean_object* v_k_1207_){
_start:
{
uint8_t v_res_1208_; lean_object* v_r_1209_; 
v_res_1208_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0(v_k_1207_);
lean_dec(v_k_1207_);
v_r_1209_ = lean_box(v_res_1208_);
return v_r_1209_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(lean_object* v_keys_1210_, lean_object* v_i_1211_, lean_object* v_k_1212_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_array_get_size(v_keys_1210_);
v___x_1214_ = lean_nat_dec_lt(v_i_1211_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_dec(v_i_1211_);
return v___x_1214_;
}
else
{
lean_object* v_k_x27_1215_; uint8_t v___x_1216_; 
v_k_x27_1215_ = lean_array_fget_borrowed(v_keys_1210_, v_i_1211_);
v___x_1216_ = l_Lean_instBEqExtraModUse_beq(v_k_1212_, v_k_x27_1215_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = lean_nat_add(v_i_1211_, v___x_1217_);
lean_dec(v_i_1211_);
v_i_1211_ = v___x_1218_;
goto _start;
}
else
{
lean_dec(v_i_1211_);
return v___x_1216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg___boxed(lean_object* v_keys_1220_, lean_object* v_i_1221_, lean_object* v_k_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(v_keys_1220_, v_i_1221_, v_k_1222_);
lean_dec_ref(v_k_1222_);
lean_dec_ref(v_keys_1220_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(lean_object* v_x_1225_, size_t v_x_1226_, lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
lean_object* v_es_1228_; lean_object* v___x_1229_; size_t v___x_1230_; size_t v___x_1231_; lean_object* v_j_1232_; lean_object* v___x_1233_; 
v_es_1228_ = lean_ctor_get(v_x_1225_, 0);
v___x_1229_ = lean_box(2);
v___x_1230_ = ((size_t)31ULL);
v___x_1231_ = lean_usize_land(v_x_1226_, v___x_1230_);
v_j_1232_ = lean_usize_to_nat(v___x_1231_);
v___x_1233_ = lean_array_get_borrowed(v___x_1229_, v_es_1228_, v_j_1232_);
lean_dec(v_j_1232_);
switch(lean_obj_tag(v___x_1233_))
{
case 0:
{
lean_object* v_key_1234_; uint8_t v___x_1235_; 
v_key_1234_ = lean_ctor_get(v___x_1233_, 0);
v___x_1235_ = l_Lean_instBEqExtraModUse_beq(v_x_1227_, v_key_1234_);
return v___x_1235_;
}
case 1:
{
lean_object* v_node_1236_; size_t v___x_1237_; size_t v___x_1238_; 
v_node_1236_ = lean_ctor_get(v___x_1233_, 0);
v___x_1237_ = ((size_t)5ULL);
v___x_1238_ = lean_usize_shift_right(v_x_1226_, v___x_1237_);
v_x_1225_ = v_node_1236_;
v_x_1226_ = v___x_1238_;
goto _start;
}
default: 
{
uint8_t v___x_1240_; 
v___x_1240_ = 0;
return v___x_1240_;
}
}
}
else
{
lean_object* v_ks_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_ks_1241_ = lean_ctor_get(v_x_1225_, 0);
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(v_ks_1241_, v___x_1242_, v_x_1227_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___boxed(lean_object* v_x_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
size_t v_x_54087__boxed_1247_; uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_x_54087__boxed_1247_ = lean_unbox_usize(v_x_1245_);
lean_dec(v_x_1245_);
v_res_1248_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(v_x_1244_, v_x_54087__boxed_1247_, v_x_1246_);
lean_dec_ref(v_x_1246_);
lean_dec_ref(v_x_1244_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(lean_object* v_x_1250_, lean_object* v_x_1251_){
_start:
{
uint64_t v___x_1252_; size_t v___x_1253_; uint8_t v___x_1254_; 
v___x_1252_ = l_Lean_instHashableExtraModUse_hash(v_x_1251_);
v___x_1253_ = lean_uint64_to_usize(v___x_1252_);
v___x_1254_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(v_x_1250_, v___x_1253_, v_x_1251_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg___boxed(lean_object* v_x_1255_, lean_object* v_x_1256_){
_start:
{
uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(v_x_1255_, v_x_1256_);
lean_dec_ref(v_x_1256_);
lean_dec_ref(v_x_1255_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1259_; double v___x_1260_; 
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = lean_float_of_nat(v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(lean_object* v_cls_1263_, lean_object* v_msg_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_ref_1270_; lean_object* v___x_1271_; lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1316_; 
v_ref_1270_ = lean_ctor_get(v___y_1267_, 5);
v___x_1271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16(v_msg_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1316_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1316_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v_traceState_1277_; lean_object* v_env_1278_; lean_object* v_nextMacroScope_1279_; lean_object* v_ngen_1280_; lean_object* v_auxDeclNGen_1281_; lean_object* v_cache_1282_; lean_object* v_messages_1283_; lean_object* v_infoState_1284_; lean_object* v_snapshotTasks_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1315_; 
v___x_1276_ = lean_st_ref_take(v___y_1268_);
v_traceState_1277_ = lean_ctor_get(v___x_1276_, 4);
v_env_1278_ = lean_ctor_get(v___x_1276_, 0);
v_nextMacroScope_1279_ = lean_ctor_get(v___x_1276_, 1);
v_ngen_1280_ = lean_ctor_get(v___x_1276_, 2);
v_auxDeclNGen_1281_ = lean_ctor_get(v___x_1276_, 3);
v_cache_1282_ = lean_ctor_get(v___x_1276_, 5);
v_messages_1283_ = lean_ctor_get(v___x_1276_, 6);
v_infoState_1284_ = lean_ctor_get(v___x_1276_, 7);
v_snapshotTasks_1285_ = lean_ctor_get(v___x_1276_, 8);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1287_ = v___x_1276_;
v_isShared_1288_ = v_isSharedCheck_1315_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_snapshotTasks_1285_);
lean_inc(v_infoState_1284_);
lean_inc(v_messages_1283_);
lean_inc(v_cache_1282_);
lean_inc(v_traceState_1277_);
lean_inc(v_auxDeclNGen_1281_);
lean_inc(v_ngen_1280_);
lean_inc(v_nextMacroScope_1279_);
lean_inc(v_env_1278_);
lean_dec(v___x_1276_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1315_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
uint64_t v_tid_1289_; lean_object* v_traces_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1314_; 
v_tid_1289_ = lean_ctor_get_uint64(v_traceState_1277_, sizeof(void*)*1);
v_traces_1290_ = lean_ctor_get(v_traceState_1277_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_traceState_1277_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1292_ = v_traceState_1277_;
v_isShared_1293_ = v_isSharedCheck_1314_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_traces_1290_);
lean_dec(v_traceState_1277_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1314_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; double v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1294_ = lean_box(0);
v___x_1295_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0);
v___x_1296_ = 0;
v___x_1297_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0));
v___x_1298_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1298_, 0, v_cls_1263_);
lean_ctor_set(v___x_1298_, 1, v___x_1294_);
lean_ctor_set(v___x_1298_, 2, v___x_1297_);
lean_ctor_set_float(v___x_1298_, sizeof(void*)*3, v___x_1295_);
lean_ctor_set_float(v___x_1298_, sizeof(void*)*3 + 8, v___x_1295_);
lean_ctor_set_uint8(v___x_1298_, sizeof(void*)*3 + 16, v___x_1296_);
v___x_1299_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1));
v___x_1300_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v_a_1272_);
lean_ctor_set(v___x_1300_, 2, v___x_1299_);
lean_inc(v_ref_1270_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v_ref_1270_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_PersistentArray_push___redArg(v_traces_1290_, v___x_1301_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1302_);
v___x_1304_ = v___x_1292_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1302_);
lean_ctor_set_uint64(v_reuseFailAlloc_1313_, sizeof(void*)*1, v_tid_1289_);
v___x_1304_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 4, v___x_1304_);
v___x_1306_ = v___x_1287_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_env_1278_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_nextMacroScope_1279_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_ngen_1280_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v_auxDeclNGen_1281_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1312_, 5, v_cache_1282_);
lean_ctor_set(v_reuseFailAlloc_1312_, 6, v_messages_1283_);
lean_ctor_set(v_reuseFailAlloc_1312_, 7, v_infoState_1284_);
lean_ctor_set(v_reuseFailAlloc_1312_, 8, v_snapshotTasks_1285_);
v___x_1306_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1307_ = lean_st_ref_set(v___y_1268_, v___x_1306_);
v___x_1308_ = lean_box(0);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1308_);
v___x_1310_ = v___x_1274_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___boxed(lean_object* v_cls_1317_, lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_1317_, v_msg_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1324_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__1));
v___x_1328_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__0));
v___x_1329_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1328_, v___x_1327_);
return v___x_1329_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__5));
v___x_1335_ = l_Lean_stringToMessageData(v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__7));
v___x_1338_ = l_Lean_stringToMessageData(v___x_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11(void){
_start:
{
lean_object* v_cls_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_cls_1343_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__4));
v___x_1344_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__10));
v___x_1345_ = l_Lean_Name_append(v___x_1344_, v_cls_1343_);
return v___x_1345_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__12));
v___x_1348_ = l_Lean_stringToMessageData(v___x_1347_);
return v___x_1348_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15(void){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__14));
v___x_1351_ = l_Lean_stringToMessageData(v___x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(lean_object* v_mod_1356_, uint8_t v_isMeta_1357_, lean_object* v_hint_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; lean_object* v_env_1367_; uint8_t v_isExporting_1368_; lean_object* v___x_1369_; lean_object* v_env_1370_; lean_object* v___x_1371_; lean_object* v_entry_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1366_ = lean_st_ref_get(v___y_1364_);
v_env_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc_ref(v_env_1367_);
lean_dec(v___x_1366_);
v_isExporting_1368_ = lean_ctor_get_uint8(v_env_1367_, sizeof(void*)*8);
lean_dec_ref(v_env_1367_);
v___x_1369_ = lean_st_ref_get(v___y_1364_);
v_env_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc_ref(v_env_1370_);
lean_dec(v___x_1369_);
v___x_1371_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2);
lean_inc(v_mod_1356_);
v_entry_1372_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1372_, 0, v_mod_1356_);
lean_ctor_set_uint8(v_entry_1372_, sizeof(void*)*1, v_isExporting_1368_);
lean_ctor_set_uint8(v_entry_1372_, sizeof(void*)*1 + 1, v_isMeta_1357_);
v___x_1373_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1374_ = lean_box(1);
v___x_1375_ = lean_box(0);
v___x_1418_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1371_, v___x_1373_, v_env_1370_, v___x_1374_, v___x_1375_);
v___x_1419_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(v___x_1418_, v_entry_1372_);
lean_dec(v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v_options_1420_; uint8_t v_hasTrace_1421_; 
v_options_1420_ = lean_ctor_get(v___y_1363_, 2);
v_hasTrace_1421_ = lean_ctor_get_uint8(v_options_1420_, sizeof(void*)*1);
if (v_hasTrace_1421_ == 0)
{
lean_dec(v_hint_1358_);
lean_dec(v_mod_1356_);
v___y_1377_ = v___y_1362_;
v___y_1378_ = v___y_1364_;
goto v___jp_1376_;
}
else
{
lean_object* v_inheritedTraceOptions_1422_; lean_object* v_cls_1423_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v_inheritedTraceOptions_1422_ = lean_ctor_get(v___y_1363_, 13);
v_cls_1423_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__4));
v___x_1443_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11);
v___x_1444_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1422_, v_options_1420_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_dec(v_hint_1358_);
lean_dec(v_mod_1356_);
v___y_1377_ = v___y_1362_;
v___y_1378_ = v___y_1364_;
goto v___jp_1376_;
}
else
{
lean_object* v___x_1445_; lean_object* v___y_1447_; 
v___x_1445_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13);
if (v_isExporting_1368_ == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__18));
v___y_1447_ = v___x_1454_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__19));
v___y_1447_ = v___x_1455_;
goto v___jp_1446_;
}
v___jp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_inc_ref(v___y_1447_);
v___x_1448_ = l_Lean_stringToMessageData(v___y_1447_);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1445_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15);
v___x_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
if (v_isMeta_1357_ == 0)
{
lean_object* v___x_1452_; 
v___x_1452_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__16));
v___y_1430_ = v___x_1451_;
v___y_1431_ = v___x_1452_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1453_; 
v___x_1453_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__17));
v___y_1430_ = v___x_1451_;
v___y_1431_ = v___x_1453_;
goto v___jp_1429_;
}
}
}
v___jp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___y_1425_);
lean_ctor_set(v___x_1427_, 1, v___y_1426_);
v___x_1428_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_1423_, v___x_1427_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_dec_ref_known(v___x_1428_, 1);
v___y_1377_ = v___y_1362_;
v___y_1378_ = v___y_1364_;
goto v___jp_1376_;
}
else
{
lean_dec_ref_known(v_entry_1372_, 1);
return v___x_1428_;
}
}
v___jp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
lean_inc_ref(v___y_1431_);
v___x_1432_ = l_Lean_stringToMessageData(v___y_1431_);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1430_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_MessageData_ofName(v_mod_1356_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = l_Lean_Name_isAnonymous(v_hint_1358_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8);
v___x_1440_ = l_Lean_MessageData_ofName(v_hint_1358_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___y_1425_ = v___x_1437_;
v___y_1426_ = v___x_1441_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1442_; 
lean_dec(v_hint_1358_);
v___x_1442_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9);
v___y_1425_ = v___x_1437_;
v___y_1426_ = v___x_1442_;
goto v___jp_1424_;
}
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec_ref_known(v_entry_1372_, 1);
lean_dec(v_hint_1358_);
lean_dec(v_mod_1356_);
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
v___jp_1376_:
{
lean_object* v___x_1379_; lean_object* v_toEnvExtension_1380_; lean_object* v_env_1381_; lean_object* v_nextMacroScope_1382_; lean_object* v_ngen_1383_; lean_object* v_auxDeclNGen_1384_; lean_object* v_traceState_1385_; lean_object* v_messages_1386_; lean_object* v_infoState_1387_; lean_object* v_snapshotTasks_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1416_; 
v___x_1379_ = lean_st_ref_take(v___y_1378_);
v_toEnvExtension_1380_ = lean_ctor_get(v___x_1373_, 0);
v_env_1381_ = lean_ctor_get(v___x_1379_, 0);
v_nextMacroScope_1382_ = lean_ctor_get(v___x_1379_, 1);
v_ngen_1383_ = lean_ctor_get(v___x_1379_, 2);
v_auxDeclNGen_1384_ = lean_ctor_get(v___x_1379_, 3);
v_traceState_1385_ = lean_ctor_get(v___x_1379_, 4);
v_messages_1386_ = lean_ctor_get(v___x_1379_, 6);
v_infoState_1387_ = lean_ctor_get(v___x_1379_, 7);
v_snapshotTasks_1388_ = lean_ctor_get(v___x_1379_, 8);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; 
v_unused_1417_ = lean_ctor_get(v___x_1379_, 5);
lean_dec(v_unused_1417_);
v___x_1390_ = v___x_1379_;
v_isShared_1391_ = v_isSharedCheck_1416_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_snapshotTasks_1388_);
lean_inc(v_infoState_1387_);
lean_inc(v_messages_1386_);
lean_inc(v_traceState_1385_);
lean_inc(v_auxDeclNGen_1384_);
lean_inc(v_ngen_1383_);
lean_inc(v_nextMacroScope_1382_);
lean_inc(v_env_1381_);
lean_dec(v___x_1379_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1416_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v_asyncMode_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v_asyncMode_1392_ = lean_ctor_get(v_toEnvExtension_1380_, 2);
v___x_1393_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1373_, v_env_1381_, v_entry_1372_, v_asyncMode_1392_, v___x_1375_);
v___x_1394_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 5, v___x_1394_);
lean_ctor_set(v___x_1390_, 0, v___x_1393_);
v___x_1396_ = v___x_1390_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_nextMacroScope_1382_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_ngen_1383_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_auxDeclNGen_1384_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_traceState_1385_);
lean_ctor_set(v_reuseFailAlloc_1415_, 5, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1415_, 6, v_messages_1386_);
lean_ctor_set(v_reuseFailAlloc_1415_, 7, v_infoState_1387_);
lean_ctor_set(v_reuseFailAlloc_1415_, 8, v_snapshotTasks_1388_);
v___x_1396_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_mctx_1399_; lean_object* v_zetaDeltaFVarIds_1400_; lean_object* v_postponed_1401_; lean_object* v_diag_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1413_; 
v___x_1397_ = lean_st_ref_set(v___y_1378_, v___x_1396_);
v___x_1398_ = lean_st_ref_take(v___y_1377_);
v_mctx_1399_ = lean_ctor_get(v___x_1398_, 0);
v_zetaDeltaFVarIds_1400_ = lean_ctor_get(v___x_1398_, 2);
v_postponed_1401_ = lean_ctor_get(v___x_1398_, 3);
v_diag_1402_ = lean_ctor_get(v___x_1398_, 4);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1398_, 1);
lean_dec(v_unused_1414_);
v___x_1404_ = v___x_1398_;
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_diag_1402_);
lean_inc(v_postponed_1401_);
lean_inc(v_zetaDeltaFVarIds_1400_);
lean_inc(v_mctx_1399_);
lean_dec(v___x_1398_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1413_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 1, v___x_1406_);
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_mctx_1399_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_zetaDeltaFVarIds_1400_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v_postponed_1401_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v_diag_1402_);
v___x_1408_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_st_ref_set(v___y_1377_, v___x_1408_);
v___x_1410_ = lean_box(0);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___boxed(lean_object* v_mod_1458_, lean_object* v_isMeta_1459_, lean_object* v_hint_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v_isMeta_boxed_1468_; lean_object* v_res_1469_; 
v_isMeta_boxed_1468_ = lean_unbox(v_isMeta_1459_);
v_res_1469_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(v_mod_1458_, v_isMeta_boxed_1468_, v_hint_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(lean_object* v___x_1470_, lean_object* v_declName_1471_, lean_object* v_as_1472_, size_t v_sz_1473_, size_t v_i_1474_, lean_object* v_b_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_usize_dec_lt(v_i_1474_, v_sz_1473_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; 
lean_dec(v_declName_1471_);
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v_b_1475_);
return v___x_1484_;
}
else
{
lean_object* v___x_1485_; lean_object* v_modules_1486_; lean_object* v___x_1487_; lean_object* v_a_1488_; lean_object* v___x_1489_; lean_object* v_toImport_1490_; lean_object* v_module_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; 
v___x_1485_ = l_Lean_Environment_header(v___x_1470_);
v_modules_1486_ = lean_ctor_get(v___x_1485_, 3);
lean_inc_ref(v_modules_1486_);
lean_dec_ref(v___x_1485_);
v___x_1487_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1488_ = lean_array_uget_borrowed(v_as_1472_, v_i_1474_);
v___x_1489_ = lean_array_get(v___x_1487_, v_modules_1486_, v_a_1488_);
lean_dec_ref(v_modules_1486_);
v_toImport_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc_ref(v_toImport_1490_);
lean_dec(v___x_1489_);
v_module_1491_ = lean_ctor_get(v_toImport_1490_, 0);
lean_inc(v_module_1491_);
lean_dec_ref(v_toImport_1490_);
v___x_1492_ = 0;
lean_inc(v_declName_1471_);
v___x_1493_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(v_module_1491_, v___x_1492_, v_declName_1471_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1494_; size_t v___x_1495_; size_t v___x_1496_; 
lean_dec_ref_known(v___x_1493_, 1);
v___x_1494_ = lean_box(0);
v___x_1495_ = ((size_t)1ULL);
v___x_1496_ = lean_usize_add(v_i_1474_, v___x_1495_);
v_i_1474_ = v___x_1496_;
v_b_1475_ = v___x_1494_;
goto _start;
}
else
{
lean_dec(v_declName_1471_);
return v___x_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18___boxed(lean_object* v___x_1498_, lean_object* v_declName_1499_, lean_object* v_as_1500_, lean_object* v_sz_1501_, lean_object* v_i_1502_, lean_object* v_b_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
size_t v_sz_boxed_1511_; size_t v_i_boxed_1512_; lean_object* v_res_1513_; 
v_sz_boxed_1511_ = lean_unbox_usize(v_sz_1501_);
lean_dec(v_sz_1501_);
v_i_boxed_1512_ = lean_unbox_usize(v_i_1502_);
lean_dec(v_i_1502_);
v_res_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(v___x_1498_, v_declName_1499_, v_as_1500_, v_sz_boxed_1511_, v_i_boxed_1512_, v_b_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec_ref(v_as_1500_);
lean_dec_ref(v___x_1498_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(lean_object* v_a_1514_, lean_object* v_x_1515_){
_start:
{
if (lean_obj_tag(v_x_1515_) == 0)
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_box(0);
return v___x_1516_;
}
else
{
lean_object* v_key_1517_; lean_object* v_value_1518_; lean_object* v_tail_1519_; uint8_t v___x_1520_; 
v_key_1517_ = lean_ctor_get(v_x_1515_, 0);
v_value_1518_ = lean_ctor_get(v_x_1515_, 1);
v_tail_1519_ = lean_ctor_get(v_x_1515_, 2);
v___x_1520_ = lean_name_eq(v_key_1517_, v_a_1514_);
if (v___x_1520_ == 0)
{
v_x_1515_ = v_tail_1519_;
goto _start;
}
else
{
lean_object* v___x_1522_; 
lean_inc(v_value_1518_);
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_value_1518_);
return v___x_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg___boxed(lean_object* v_a_1523_, lean_object* v_x_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(v_a_1523_, v_x_1524_);
lean_dec(v_x_1524_);
lean_dec(v_a_1523_);
return v_res_1525_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1526_; uint64_t v___x_1527_; 
v___x_1526_ = lean_unsigned_to_nat(1723u);
v___x_1527_ = lean_uint64_of_nat(v___x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(lean_object* v_m_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v_buckets_1530_; lean_object* v___x_1531_; uint64_t v___y_1533_; 
v_buckets_1530_ = lean_ctor_get(v_m_1528_, 1);
v___x_1531_ = lean_array_get_size(v_buckets_1530_);
if (lean_obj_tag(v_a_1529_) == 0)
{
uint64_t v___x_1547_; 
v___x_1547_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0);
v___y_1533_ = v___x_1547_;
goto v___jp_1532_;
}
else
{
uint64_t v_hash_1548_; 
v_hash_1548_ = lean_ctor_get_uint64(v_a_1529_, sizeof(void*)*2);
v___y_1533_ = v_hash_1548_;
goto v___jp_1532_;
}
v___jp_1532_:
{
uint64_t v___x_1534_; uint64_t v___x_1535_; uint64_t v_fold_1536_; uint64_t v___x_1537_; uint64_t v___x_1538_; uint64_t v___x_1539_; size_t v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; size_t v___x_1543_; size_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1534_ = 32ULL;
v___x_1535_ = lean_uint64_shift_right(v___y_1533_, v___x_1534_);
v_fold_1536_ = lean_uint64_xor(v___y_1533_, v___x_1535_);
v___x_1537_ = 16ULL;
v___x_1538_ = lean_uint64_shift_right(v_fold_1536_, v___x_1537_);
v___x_1539_ = lean_uint64_xor(v_fold_1536_, v___x_1538_);
v___x_1540_ = lean_uint64_to_usize(v___x_1539_);
v___x_1541_ = lean_usize_of_nat(v___x_1531_);
v___x_1542_ = ((size_t)1ULL);
v___x_1543_ = lean_usize_sub(v___x_1541_, v___x_1542_);
v___x_1544_ = lean_usize_land(v___x_1540_, v___x_1543_);
v___x_1545_ = lean_array_uget_borrowed(v_buckets_1530_, v___x_1544_);
v___x_1546_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(v_a_1529_, v___x_1545_);
return v___x_1546_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___boxed(lean_object* v_m_1549_, lean_object* v_a_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(v_m_1549_, v_a_1550_);
lean_dec(v_a_1550_);
lean_dec_ref(v_m_1549_);
return v_res_1551_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__1));
v___x_1555_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__0));
v___x_1556_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1555_, v___x_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(lean_object* v_declName_1559_, uint8_t v_isMeta_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; lean_object* v_env_1572_; lean_object* v___y_1574_; lean_object* v___x_1587_; 
v___x_1568_ = lean_st_ref_get(v___y_1566_);
v_env_1572_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_ref(v_env_1572_);
lean_dec(v___x_1568_);
v___x_1587_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1572_, v_declName_1559_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_dec_ref(v_env_1572_);
lean_dec(v_declName_1559_);
goto v___jp_1569_;
}
else
{
lean_object* v_val_1588_; lean_object* v___x_1589_; lean_object* v_modules_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v_val_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l_Lean_Environment_header(v_env_1572_);
v_modules_1590_ = lean_ctor_get(v___x_1589_, 3);
lean_inc_ref(v_modules_1590_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = lean_array_get_size(v_modules_1590_);
v___x_1592_ = lean_nat_dec_lt(v_val_1588_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_dec_ref(v_modules_1590_);
lean_dec(v_val_1588_);
lean_dec_ref(v_env_1572_);
lean_dec(v_declName_1559_);
goto v___jp_1569_;
}
else
{
lean_object* v___x_1593_; lean_object* v_env_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___y_1598_; 
v___x_1593_ = lean_st_ref_get(v___y_1566_);
v_env_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc_ref(v_env_1594_);
lean_dec(v___x_1593_);
v___x_1595_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2);
v___x_1596_ = lean_array_fget(v_modules_1590_, v_val_1588_);
lean_dec(v_val_1588_);
lean_dec_ref(v_modules_1590_);
if (v_isMeta_1560_ == 0)
{
lean_dec_ref(v_env_1594_);
v___y_1598_ = v_isMeta_1560_;
goto v___jp_1597_;
}
else
{
uint8_t v___x_1609_; 
lean_inc(v_declName_1559_);
v___x_1609_ = l_Lean_isMarkedMeta(v_env_1594_, v_declName_1559_);
if (v___x_1609_ == 0)
{
v___y_1598_ = v_isMeta_1560_;
goto v___jp_1597_;
}
else
{
uint8_t v___x_1610_; 
v___x_1610_ = 0;
v___y_1598_ = v___x_1610_;
goto v___jp_1597_;
}
}
v___jp_1597_:
{
lean_object* v_toImport_1599_; lean_object* v_module_1600_; lean_object* v___x_1601_; 
v_toImport_1599_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_ref(v_toImport_1599_);
lean_dec(v___x_1596_);
v_module_1600_ = lean_ctor_get(v_toImport_1599_, 0);
lean_inc(v_module_1600_);
lean_dec_ref(v_toImport_1599_);
lean_inc(v_declName_1559_);
v___x_1601_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(v_module_1600_, v___y_1598_, v_declName_1559_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec_ref_known(v___x_1601_, 1);
v___x_1602_ = l_Lean_indirectModUseExt;
v___x_1603_ = lean_box(1);
v___x_1604_ = lean_box(0);
lean_inc_ref(v_env_1572_);
v___x_1605_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1595_, v___x_1602_, v_env_1572_, v___x_1603_, v___x_1604_);
v___x_1606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(v___x_1605_, v_declName_1559_);
lean_dec(v___x_1605_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1607_; 
v___x_1607_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__3));
v___y_1574_ = v___x_1607_;
goto v___jp_1573_;
}
else
{
lean_object* v_val_1608_; 
v_val_1608_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v___x_1606_, 1);
v___y_1574_ = v_val_1608_;
goto v___jp_1573_;
}
}
else
{
lean_dec_ref(v_env_1572_);
lean_dec(v_declName_1559_);
return v___x_1601_;
}
}
}
}
v___jp_1569_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = lean_box(0);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
v___jp_1573_:
{
lean_object* v___x_1575_; size_t v_sz_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1575_ = lean_box(0);
v_sz_1576_ = lean_array_size(v___y_1574_);
v___x_1577_ = ((size_t)0ULL);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(v_env_1572_, v_declName_1559_, v___y_1574_, v_sz_1576_, v___x_1577_, v___x_1575_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec_ref(v___y_1574_);
lean_dec_ref(v_env_1572_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v___x_1578_, 0);
lean_dec(v_unused_1586_);
v___x_1580_ = v___x_1578_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_dec(v___x_1578_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1575_);
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1575_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___boxed(lean_object* v_declName_1611_, lean_object* v_isMeta_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
uint8_t v_isMeta_boxed_1620_; lean_object* v_res_1621_; 
v_isMeta_boxed_1620_ = lean_unbox(v_isMeta_1612_);
v_res_1621_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v_declName_1611_, v_isMeta_boxed_1620_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(lean_object* v_as_x27_1622_, lean_object* v_b_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
if (lean_obj_tag(v_as_x27_1622_) == 0)
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_b_1623_);
return v___x_1631_;
}
else
{
lean_object* v_head_1632_; lean_object* v_tail_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; 
v_head_1632_ = lean_ctor_get(v_as_x27_1622_, 0);
v_tail_1633_ = lean_ctor_get(v_as_x27_1622_, 1);
v___x_1634_ = 1;
lean_inc(v_head_1632_);
v___x_1635_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v_head_1632_, v___x_1634_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref_known(v___x_1635_, 1);
v___x_1636_ = lean_box(0);
v_as_x27_1622_ = v_tail_1633_;
v_b_1623_ = v___x_1636_;
goto _start;
}
else
{
return v___x_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg___boxed(lean_object* v_as_x27_1638_, lean_object* v_b_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(v_as_x27_1638_, v_b_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v_as_x27_1638_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(lean_object* v_x_1648_, lean_object* v___y_1649_){
_start:
{
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v_x_1648_, 0);
lean_inc(v_a_1650_);
v___x_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1651_, 0, v_a_1650_);
lean_ctor_set(v___x_1651_, 1, v___y_1649_);
return v___x_1651_;
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1653_; 
v_a_1652_ = lean_ctor_get(v_x_1648_, 0);
lean_inc(v_a_1652_);
v___x_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1653_, 0, v_a_1652_);
lean_ctor_set(v___x_1653_, 1, v___y_1649_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___boxed(lean_object* v_x_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_x_1654_, v___y_1655_);
lean_dec_ref(v_x_1654_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(lean_object* v_env_1657_, lean_object* v_stx_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1657_, v_stx_1658_, v___y_1659_, v___y_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
if (lean_obj_tag(v_a_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1671_; 
v_a_1663_ = lean_ctor_get(v___x_1661_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v___x_1661_, 0);
lean_dec(v_unused_1672_);
v___x_1665_ = v___x_1661_;
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1661_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1671_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1667_ = lean_box(0);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1667_);
v___x_1669_ = v___x_1665_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_a_1663_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
lean_object* v_val_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1701_; 
v_val_1673_ = lean_ctor_get(v_a_1662_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_a_1662_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1675_ = v_a_1662_;
v_isShared_1676_ = v_isSharedCheck_1701_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_val_1673_);
lean_dec(v_a_1662_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1701_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_snd_1677_; 
v_snd_1677_ = lean_ctor_get(v_val_1673_, 1);
lean_inc(v_snd_1677_);
lean_dec(v_val_1673_);
if (lean_obj_tag(v_snd_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1687_; 
lean_del_object(v___x_1675_);
v_a_1678_ = lean_ctor_get(v___x_1661_, 1);
lean_inc(v_a_1678_);
lean_dec_ref_known(v___x_1661_, 2);
v_a_1679_ = lean_ctor_get(v_snd_1677_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_snd_1677_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1681_ = v_snd_1677_;
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v_snd_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v___x_1684_, v_a_1678_);
lean_dec_ref(v___x_1684_);
return v___x_1685_;
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1700_; 
v_a_1688_ = lean_ctor_get(v___x_1661_, 1);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1661_, 2);
v_a_1689_ = lean_ctor_get(v_snd_1677_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_snd_1677_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1691_ = v_snd_1677_;
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v_snd_1677_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v_a_1689_);
v___x_1694_ = v___x_1675_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1696_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1694_);
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v___x_1696_, v_a_1688_);
lean_dec_ref(v___x_1696_);
return v___x_1697_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
v_a_1702_ = lean_ctor_get(v___x_1661_, 0);
v_a_1703_ = lean_ctor_get(v___x_1661_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1661_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_inc(v_a_1702_);
lean_dec(v___x_1661_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1702_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed(lean_object* v_env_1711_, lean_object* v_stx_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(v_env_1711_, v_stx_1712_, v___y_1713_, v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(lean_object* v_env_1716_, lean_object* v_options_1717_, lean_object* v_currNamespace_1718_, lean_object* v_openDecls_1719_, lean_object* v_n_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = l_Lean_ResolveName_resolveGlobalName(v_env_1716_, v_options_1717_, v_currNamespace_1718_, v_openDecls_1719_, v_n_1720_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___y_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed(lean_object* v_env_1725_, lean_object* v_options_1726_, lean_object* v_currNamespace_1727_, lean_object* v_openDecls_1728_, lean_object* v_n_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(v_env_1725_, v_options_1726_, v_currNamespace_1727_, v_openDecls_1728_, v_n_1729_, v___y_1730_, v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v_options_1726_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(lean_object* v_currNamespace_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v_currNamespace_1733_);
lean_ctor_set(v___x_1736_, 1, v___y_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed(lean_object* v_currNamespace_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(v_currNamespace_1737_, v___y_1738_, v___y_1739_);
lean_dec_ref(v___y_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(lean_object* v_env_1741_, lean_object* v_declName_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v___x_1745_; lean_object* v_env_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; uint8_t v___x_1749_; 
v___x_1745_ = 0;
v_env_1746_ = l_Lean_Environment_setExporting(v_env_1741_, v___x_1745_);
lean_inc(v_declName_1742_);
v___x_1747_ = l_Lean_mkPrivateName(v_env_1746_, v_declName_1742_);
v___x_1748_ = 1;
lean_inc_ref(v_env_1746_);
v___x_1749_ = l_Lean_Environment_contains(v_env_1746_, v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1750_ = l_Lean_privateToUserName(v_declName_1742_);
v___x_1751_ = l_Lean_Environment_contains(v_env_1746_, v___x_1750_, v___x_1748_);
v___x_1752_ = lean_box(v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___y_1744_);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec_ref(v_env_1746_);
lean_dec(v_declName_1742_);
v___x_1754_ = lean_box(v___x_1749_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___y_1744_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed(lean_object* v_env_1756_, lean_object* v_declName_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(v_env_1756_, v_declName_1757_, v___y_1758_, v___y_1759_);
lean_dec_ref(v___y_1758_);
return v_res_1760_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = l_Lean_maxRecDepthErrorMessage;
v___x_1767_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3);
v___x_1769_ = l_Lean_MessageData_ofFormat(v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4);
v___x_1771_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__2));
v___x_1772_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
lean_ctor_set(v___x_1772_, 1, v___x_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(lean_object* v_ref_1773_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_ref_1773_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___boxed(lean_object* v_ref_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(v_ref_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(lean_object* v_env_1781_, lean_object* v_currNamespace_1782_, lean_object* v_openDecls_1783_, lean_object* v_n_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = l_Lean_ResolveName_resolveNamespace(v_env_1781_, v_currNamespace_1782_, v_openDecls_1783_, v_n_1784_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
lean_ctor_set(v___x_1788_, 1, v___y_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed(lean_object* v_env_1789_, lean_object* v_currNamespace_1790_, lean_object* v_openDecls_1791_, lean_object* v_n_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(v_env_1789_, v_currNamespace_1790_, v_openDecls_1791_, v_n_1792_, v___y_1793_, v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(lean_object* v_as_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
if (lean_obj_tag(v_as_1796_) == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = lean_box(0);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
return v___x_1805_;
}
else
{
lean_object* v_options_1806_; uint8_t v_hasTrace_1807_; 
v_options_1806_ = lean_ctor_get(v___y_1801_, 2);
v_hasTrace_1807_ = lean_ctor_get_uint8(v_options_1806_, sizeof(void*)*1);
if (v_hasTrace_1807_ == 0)
{
lean_object* v_tail_1808_; 
v_tail_1808_ = lean_ctor_get(v_as_1796_, 1);
lean_inc(v_tail_1808_);
lean_dec_ref_known(v_as_1796_, 2);
v_as_1796_ = v_tail_1808_;
goto _start;
}
else
{
lean_object* v_head_1810_; lean_object* v_tail_1811_; lean_object* v_fst_1812_; lean_object* v_snd_1813_; lean_object* v_inheritedTraceOptions_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_head_1810_ = lean_ctor_get(v_as_1796_, 0);
lean_inc(v_head_1810_);
v_tail_1811_ = lean_ctor_get(v_as_1796_, 1);
lean_inc(v_tail_1811_);
lean_dec_ref_known(v_as_1796_, 2);
v_fst_1812_ = lean_ctor_get(v_head_1810_, 0);
lean_inc_n(v_fst_1812_, 2);
v_snd_1813_ = lean_ctor_get(v_head_1810_, 1);
lean_inc(v_snd_1813_);
lean_dec(v_head_1810_);
v_inheritedTraceOptions_1814_ = lean_ctor_get(v___y_1801_, 13);
v___x_1815_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__10));
v___x_1816_ = l_Lean_Name_append(v___x_1815_, v_fst_1812_);
v___x_1817_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1814_, v_options_1806_, v___x_1816_);
lean_dec(v___x_1816_);
if (v___x_1817_ == 0)
{
lean_dec(v_snd_1813_);
lean_dec(v_fst_1812_);
v_as_1796_ = v_tail_1811_;
goto _start;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_snd_1813_);
v___x_1820_ = l_Lean_MessageData_ofFormat(v___x_1819_);
v___x_1821_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_fst_1812_, v___x_1820_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_dec_ref_known(v___x_1821_, 1);
v_as_1796_ = v_tail_1811_;
goto _start;
}
else
{
lean_dec(v_tail_1811_);
return v___x_1821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___boxed(lean_object* v_as_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(v_as_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(lean_object* v_x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v_env_1842_; lean_object* v_options_1843_; lean_object* v_currRecDepth_1844_; lean_object* v_maxRecDepth_1845_; lean_object* v_ref_1846_; lean_object* v_currNamespace_1847_; lean_object* v_openDecls_1848_; lean_object* v_quotContext_1849_; lean_object* v_currMacroScope_1850_; lean_object* v___x_1851_; lean_object* v_nextMacroScope_1852_; lean_object* v___f_1853_; lean_object* v___f_1854_; lean_object* v___f_1855_; lean_object* v___f_1856_; lean_object* v___f_1857_; lean_object* v_methods_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1841_ = lean_st_ref_get(v___y_1839_);
v_env_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc_ref_n(v_env_1842_, 4);
lean_dec(v___x_1841_);
v_options_1843_ = lean_ctor_get(v___y_1838_, 2);
v_currRecDepth_1844_ = lean_ctor_get(v___y_1838_, 3);
v_maxRecDepth_1845_ = lean_ctor_get(v___y_1838_, 4);
v_ref_1846_ = lean_ctor_get(v___y_1838_, 5);
v_currNamespace_1847_ = lean_ctor_get(v___y_1838_, 6);
v_openDecls_1848_ = lean_ctor_get(v___y_1838_, 7);
v_quotContext_1849_ = lean_ctor_get(v___y_1838_, 10);
v_currMacroScope_1850_ = lean_ctor_get(v___y_1838_, 11);
v___x_1851_ = lean_st_ref_get(v___y_1839_);
v_nextMacroScope_1852_ = lean_ctor_get(v___x_1851_, 1);
lean_inc(v_nextMacroScope_1852_);
lean_dec(v___x_1851_);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1853_, 0, v_env_1842_);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1854_, 0, v_env_1842_);
lean_inc_n(v_openDecls_1848_, 2);
lean_inc_n(v_currNamespace_1847_, 3);
v___f_1855_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1855_, 0, v_env_1842_);
lean_closure_set(v___f_1855_, 1, v_currNamespace_1847_);
lean_closure_set(v___f_1855_, 2, v_openDecls_1848_);
v___f_1856_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1856_, 0, v_currNamespace_1847_);
lean_inc_ref(v_options_1843_);
v___f_1857_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1857_, 0, v_env_1842_);
lean_closure_set(v___f_1857_, 1, v_options_1843_);
lean_closure_set(v___f_1857_, 2, v_currNamespace_1847_);
lean_closure_set(v___f_1857_, 3, v_openDecls_1848_);
v_methods_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1858_, 0, v___f_1853_);
lean_ctor_set(v_methods_1858_, 1, v___f_1856_);
lean_ctor_set(v_methods_1858_, 2, v___f_1854_);
lean_ctor_set(v_methods_1858_, 3, v___f_1855_);
lean_ctor_set(v_methods_1858_, 4, v___f_1857_);
lean_inc(v_ref_1846_);
lean_inc(v_maxRecDepth_1845_);
lean_inc(v_currRecDepth_1844_);
lean_inc(v_currMacroScope_1850_);
lean_inc(v_quotContext_1849_);
v___x_1859_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1859_, 0, v_methods_1858_);
lean_ctor_set(v___x_1859_, 1, v_quotContext_1849_);
lean_ctor_set(v___x_1859_, 2, v_currMacroScope_1850_);
lean_ctor_set(v___x_1859_, 3, v_currRecDepth_1844_);
lean_ctor_set(v___x_1859_, 4, v_maxRecDepth_1845_);
lean_ctor_set(v___x_1859_, 5, v_ref_1846_);
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1861_, 0, v_nextMacroScope_1852_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
lean_ctor_set(v___x_1861_, 2, v___x_1860_);
v___x_1862_ = lean_apply_2(v_x_1833_, v___x_1859_, v___x_1861_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v_a_1864_; lean_object* v_macroScope_1865_; lean_object* v_traceMsgs_1866_; lean_object* v_expandedMacroDecls_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 1);
lean_inc(v_a_1863_);
v_a_1864_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1862_, 2);
v_macroScope_1865_ = lean_ctor_get(v_a_1863_, 0);
lean_inc(v_macroScope_1865_);
v_traceMsgs_1866_ = lean_ctor_get(v_a_1863_, 1);
lean_inc(v_traceMsgs_1866_);
v_expandedMacroDecls_1867_ = lean_ctor_get(v_a_1863_, 2);
lean_inc(v_expandedMacroDecls_1867_);
lean_dec(v_a_1863_);
v___x_1868_ = lean_box(0);
v___x_1869_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(v_expandedMacroDecls_1867_, v___x_1868_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v_expandedMacroDecls_1867_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v___x_1870_; lean_object* v_env_1871_; lean_object* v_ngen_1872_; lean_object* v_auxDeclNGen_1873_; lean_object* v_traceState_1874_; lean_object* v_cache_1875_; lean_object* v_messages_1876_; lean_object* v_infoState_1877_; lean_object* v_snapshotTasks_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref_known(v___x_1869_, 1);
v___x_1870_ = lean_st_ref_take(v___y_1839_);
v_env_1871_ = lean_ctor_get(v___x_1870_, 0);
v_ngen_1872_ = lean_ctor_get(v___x_1870_, 2);
v_auxDeclNGen_1873_ = lean_ctor_get(v___x_1870_, 3);
v_traceState_1874_ = lean_ctor_get(v___x_1870_, 4);
v_cache_1875_ = lean_ctor_get(v___x_1870_, 5);
v_messages_1876_ = lean_ctor_get(v___x_1870_, 6);
v_infoState_1877_ = lean_ctor_get(v___x_1870_, 7);
v_snapshotTasks_1878_ = lean_ctor_get(v___x_1870_, 8);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; 
v_unused_1905_ = lean_ctor_get(v___x_1870_, 1);
lean_dec(v_unused_1905_);
v___x_1880_ = v___x_1870_;
v_isShared_1881_ = v_isSharedCheck_1904_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_snapshotTasks_1878_);
lean_inc(v_infoState_1877_);
lean_inc(v_messages_1876_);
lean_inc(v_cache_1875_);
lean_inc(v_traceState_1874_);
lean_inc(v_auxDeclNGen_1873_);
lean_inc(v_ngen_1872_);
lean_inc(v_env_1871_);
lean_dec(v___x_1870_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1904_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 1, v_macroScope_1865_);
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_env_1871_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_macroScope_1865_);
lean_ctor_set(v_reuseFailAlloc_1903_, 2, v_ngen_1872_);
lean_ctor_set(v_reuseFailAlloc_1903_, 3, v_auxDeclNGen_1873_);
lean_ctor_set(v_reuseFailAlloc_1903_, 4, v_traceState_1874_);
lean_ctor_set(v_reuseFailAlloc_1903_, 5, v_cache_1875_);
lean_ctor_set(v_reuseFailAlloc_1903_, 6, v_messages_1876_);
lean_ctor_set(v_reuseFailAlloc_1903_, 7, v_infoState_1877_);
lean_ctor_set(v_reuseFailAlloc_1903_, 8, v_snapshotTasks_1878_);
v___x_1883_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_st_ref_set(v___y_1839_, v___x_1883_);
v___x_1885_ = l_List_reverse___redArg(v_traceMsgs_1866_);
v___x_1886_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(v___x_1885_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1886_, 0);
lean_dec(v_unused_1894_);
v___x_1888_ = v___x_1886_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v___x_1886_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v_a_1864_);
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1864_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec(v_a_1864_);
v_a_1895_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1886_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1886_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_traceMsgs_1866_);
lean_dec(v_macroScope_1865_);
lean_dec(v_a_1864_);
v_a_1906_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1869_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1869_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; 
v_a_1914_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1862_, 2);
if (lean_obj_tag(v_a_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v_a_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_a_1915_ = lean_ctor_get(v_a_1914_, 0);
lean_inc(v_a_1915_);
v_a_1916_ = lean_ctor_get(v_a_1914_, 1);
lean_inc_ref(v_a_1916_);
lean_dec_ref_known(v_a_1914_, 2);
v___x_1917_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0));
v___x_1918_ = lean_string_dec_eq(v_a_1916_, v___x_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1919_, 0, v_a_1916_);
v___x_1920_ = l_Lean_MessageData_ofFormat(v___x_1919_);
v___x_1921_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_a_1915_, v___x_1920_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v_a_1915_);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; 
lean_dec_ref(v_a_1916_);
v___x_1922_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(v_a_1915_);
return v___x_1922_;
}
}
else
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
return v___x_1923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___boxed(lean_object* v_x_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v_x_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1932_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__0));
v___x_1935_ = l_Lean_stringToMessageData(v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__2));
v___x_1938_ = l_Lean_stringToMessageData(v___x_1937_);
return v___x_1938_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__4));
v___x_1941_ = l_Lean_stringToMessageData(v___x_1940_);
return v___x_1941_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6));
v___x_1944_ = l_Lean_stringToMessageData(v___x_1943_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8));
v___x_1947_ = l_Lean_stringToMessageData(v___x_1946_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__10));
v___x_1950_ = l_Lean_stringToMessageData(v___x_1949_);
return v___x_1950_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__15));
v___x_1960_ = l_Lean_stringToMessageData(v___x_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1(lean_object* v___x_1961_, lean_object* v_attrInstance_1962_, lean_object* v___f_1963_, lean_object* v___x_1964_, lean_object* v___x_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_1961_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; lean_object* v_attr_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = lean_unsigned_to_nat(1u);
v_attr_1976_ = l_Lean_Syntax_getArg(v_attrInstance_1962_, v___x_1975_);
v___x_1977_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_1977_, 0, v_attr_1976_);
lean_closure_set(v___x_1977_, 1, v___f_1963_);
v___x_1978_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_1977_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2093_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_2093_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2093_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___y_1984_; uint8_t v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v_attrName_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
lean_inc(v_a_1979_);
v___x_2074_ = l_Lean_Syntax_getKind(v_a_1979_);
v___x_2075_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14));
v___x_2076_ = lean_name_eq(v___x_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
if (lean_obj_tag(v___x_2074_) == 1)
{
lean_object* v_str_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_str_2077_ = lean_ctor_get(v___x_2074_, 1);
lean_inc_ref(v_str_2077_);
lean_dec_ref_known(v___x_2074_, 2);
v___x_2078_ = lean_box(0);
v___x_2079_ = l_Lean_Name_str___override(v___x_2078_, v_str_2077_);
v_attrName_2010_ = v___x_2079_;
v___y_2011_ = v___y_1966_;
v___y_2012_ = v___y_1967_;
v___y_2013_ = v___y_1968_;
v___y_2014_ = v___y_1969_;
v___y_2015_ = v___y_1970_;
v___y_2016_ = v___y_1971_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec(v___x_2074_);
lean_del_object(v___x_1981_);
lean_dec(v_a_1974_);
lean_dec(v___x_1964_);
v___x_2080_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16);
v___x_2081_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_a_1979_, v___x_2080_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v_a_1979_);
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_dec(v___x_2074_);
v___x_2090_ = l_Lean_Syntax_getArg(v_a_1979_, v___x_1965_);
v___x_2091_ = l_Lean_Syntax_getId(v___x_2090_);
lean_dec(v___x_2090_);
v___x_2092_ = lean_erase_macro_scopes(v___x_2091_);
v_attrName_2010_ = v___x_2092_;
v___y_2011_ = v___y_1966_;
v___y_2012_ = v___y_1967_;
v___y_2013_ = v___y_1968_;
v___y_2014_ = v___y_1969_;
v___y_2015_ = v___y_1970_;
v___y_2016_ = v___y_1971_;
goto v___jp_2009_;
}
v___jp_1983_:
{
lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1988_; 
v___x_1985_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1985_, 0, v___y_1984_);
lean_ctor_set(v___x_1985_, 1, v_a_1979_);
v___x_1986_ = lean_unbox(v_a_1974_);
lean_dec(v_a_1974_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*2, v___x_1986_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1985_);
v___x_1988_ = v___x_1981_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1985_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
v___jp_1990_:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v___y_1993_, v___y_1991_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_dec_ref_known(v___x_2000_, 1);
v___y_1984_ = v___y_1992_;
goto v___jp_1983_;
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v___y_1992_);
lean_del_object(v___x_1981_);
lean_dec(v_a_1979_);
lean_dec(v_a_1974_);
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
v___jp_2009_:
{
lean_object* v___x_2017_; lean_object* v_env_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_st_ref_get(v___y_2016_);
v_env_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc_ref(v_env_2018_);
lean_dec(v___x_2017_);
lean_inc(v_attrName_2010_);
v___x_2019_ = l_Lean_getAttributeImpl(v_env_2018_, v_attrName_2010_);
if (lean_obj_tag(v___x_2019_) == 1)
{
lean_object* v___x_2020_; lean_object* v_env_2021_; lean_object* v___x_2022_; 
lean_dec_ref_known(v___x_2019_, 1);
v___x_2020_ = lean_st_ref_get(v___y_2016_);
v_env_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc_ref(v_env_2021_);
lean_dec(v___x_2020_);
lean_inc(v_attrName_2010_);
v___x_2022_ = l_Lean_getAttributeImpl(v_env_2021_, v_attrName_2010_);
if (lean_obj_tag(v___x_2022_) == 1)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; lean_object* v_toAttributeImplCore_2025_; lean_object* v_env_2026_; lean_object* v_ref_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = lean_st_ref_get(v___y_2016_);
v_toAttributeImplCore_2025_ = lean_ctor_get(v_a_2023_, 0);
lean_inc_ref(v_toAttributeImplCore_2025_);
lean_dec(v_a_2023_);
v_env_2026_ = lean_ctor_get(v___x_2024_, 0);
lean_inc_ref(v_env_2026_);
lean_dec(v___x_2024_);
v_ref_2027_ = lean_ctor_get(v_toAttributeImplCore_2025_, 0);
lean_inc_n(v_ref_2027_, 2);
lean_dec_ref(v_toAttributeImplCore_2025_);
v___x_2028_ = l_Lean_regularInitAttr;
v___x_2029_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1964_, v___x_2028_, v_env_2026_, v_ref_2027_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_dec(v_ref_2027_);
v___y_1984_ = v_attrName_2010_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2030_; lean_object* v_env_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; 
lean_dec_ref_known(v___x_2029_, 1);
v___x_2030_ = lean_st_ref_get(v___y_2016_);
v_env_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc_ref(v_env_2031_);
lean_dec(v___x_2030_);
v___x_2032_ = 1;
v___x_2033_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2031_, v_ref_2027_);
lean_dec_ref(v_env_2031_);
if (lean_obj_tag(v___x_2033_) == 1)
{
lean_object* v_val_2034_; lean_object* v___x_2035_; lean_object* v_env_2036_; lean_object* v___x_2037_; lean_object* v_modules_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v_val_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = lean_st_ref_get(v___y_2016_);
v_env_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc_ref(v_env_2036_);
lean_dec(v___x_2035_);
v___x_2037_ = l_Lean_Environment_header(v_env_2036_);
lean_dec_ref(v_env_2036_);
v_modules_2038_ = lean_ctor_get(v___x_2037_, 3);
lean_inc_ref(v_modules_2038_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = lean_array_get_size(v_modules_2038_);
v___x_2040_ = lean_nat_dec_lt(v_val_2034_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_dec_ref(v_modules_2038_);
lean_dec(v_val_2034_);
v___y_1991_ = v___x_2032_;
v___y_1992_ = v_attrName_2010_;
v___y_1993_ = v_ref_2027_;
v___y_1994_ = v___y_2011_;
v___y_1995_ = v___y_2012_;
v___y_1996_ = v___y_2013_;
v___y_1997_ = v___y_2014_;
v___y_1998_ = v___y_2015_;
v___y_1999_ = v___y_2016_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2041_; uint8_t v_hasData_2042_; 
v___x_2041_ = lean_array_fget_borrowed(v_modules_2038_, v_val_2034_);
v_hasData_2042_ = lean_ctor_get_uint8(v___x_2041_, sizeof(void*)*1 + 1);
if (v_hasData_2042_ == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v_toImport_2045_; lean_object* v_module_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_ref_2027_);
lean_del_object(v___x_1981_);
lean_dec(v_a_1979_);
lean_dec(v_a_1974_);
v___x_2043_ = l_Lean_instInhabitedEffectiveImport_default;
v___x_2044_ = lean_array_get(v___x_2043_, v_modules_2038_, v_val_2034_);
lean_dec(v_val_2034_);
lean_dec_ref(v_modules_2038_);
v_toImport_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc_ref(v_toImport_2045_);
lean_dec(v___x_2044_);
v_module_2046_ = lean_ctor_get(v_toImport_2045_, 0);
lean_inc(v_module_2046_);
lean_dec_ref(v_toImport_2045_);
v___x_2047_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1);
v___x_2048_ = l_Lean_MessageData_ofName(v_attrName_2010_);
v___x_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = l_Lean_MessageData_ofName(v_module_2046_);
lean_inc_ref(v___x_2052_);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5);
v___x_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2053_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v___x_2052_);
v___x_2057_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7);
v___x_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2056_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2058_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
lean_dec_ref(v_modules_2038_);
lean_dec(v_val_2034_);
v___y_1991_ = v___x_2032_;
v___y_1992_ = v_attrName_2010_;
v___y_1993_ = v_ref_2027_;
v___y_1994_ = v___y_2011_;
v___y_1995_ = v___y_2012_;
v___y_1996_ = v___y_2013_;
v___y_1997_ = v___y_2014_;
v___y_1998_ = v___y_2015_;
v___y_1999_ = v___y_2016_;
goto v___jp_1990_;
}
}
}
else
{
lean_dec(v___x_2033_);
v___y_1991_ = v___x_2032_;
v___y_1992_ = v_attrName_2010_;
v___y_1993_ = v_ref_2027_;
v___y_1994_ = v___y_2011_;
v___y_1995_ = v___y_2012_;
v___y_1996_ = v___y_2013_;
v___y_1997_ = v___y_2014_;
v___y_1998_ = v___y_2015_;
v___y_1999_ = v___y_2016_;
goto v___jp_1990_;
}
}
}
else
{
lean_dec_ref(v___x_2022_);
lean_dec(v___x_1964_);
v___y_1984_ = v_attrName_2010_;
goto v___jp_1983_;
}
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref(v___x_2019_);
lean_del_object(v___x_1981_);
lean_dec(v_a_1979_);
lean_dec(v_a_1974_);
lean_dec(v___x_1964_);
v___x_2068_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9);
v___x_2069_ = l_Lean_MessageData_ofName(v_attrName_2010_);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2072_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_a_1974_);
lean_dec(v___x_1964_);
v_a_2094_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_1978_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_1978_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v___x_1964_);
lean_dec_ref(v___f_1963_);
v_a_2102_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_1973_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_1973_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___boxed(lean_object* v___x_2110_, lean_object* v_attrInstance_2111_, lean_object* v___f_2112_, lean_object* v___x_2113_, lean_object* v___x_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1(v___x_2110_, v_attrInstance_2111_, v___f_2112_, v___x_2113_, v___x_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___x_2114_);
lean_dec(v_attrInstance_2111_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(lean_object* v___y_2123_, uint8_t v_isExporting_2124_, lean_object* v___x_2125_, lean_object* v___y_2126_, lean_object* v___x_2127_, lean_object* v_a_x3f_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v_env_2131_; lean_object* v_nextMacroScope_2132_; lean_object* v_ngen_2133_; lean_object* v_auxDeclNGen_2134_; lean_object* v_traceState_2135_; lean_object* v_messages_2136_; lean_object* v_infoState_2137_; lean_object* v_snapshotTasks_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2163_; 
v___x_2130_ = lean_st_ref_take(v___y_2123_);
v_env_2131_ = lean_ctor_get(v___x_2130_, 0);
v_nextMacroScope_2132_ = lean_ctor_get(v___x_2130_, 1);
v_ngen_2133_ = lean_ctor_get(v___x_2130_, 2);
v_auxDeclNGen_2134_ = lean_ctor_get(v___x_2130_, 3);
v_traceState_2135_ = lean_ctor_get(v___x_2130_, 4);
v_messages_2136_ = lean_ctor_get(v___x_2130_, 6);
v_infoState_2137_ = lean_ctor_get(v___x_2130_, 7);
v_snapshotTasks_2138_ = lean_ctor_get(v___x_2130_, 8);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v___x_2130_, 5);
lean_dec(v_unused_2164_);
v___x_2140_ = v___x_2130_;
v_isShared_2141_ = v_isSharedCheck_2163_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_snapshotTasks_2138_);
lean_inc(v_infoState_2137_);
lean_inc(v_messages_2136_);
lean_inc(v_traceState_2135_);
lean_inc(v_auxDeclNGen_2134_);
lean_inc(v_ngen_2133_);
lean_inc(v_nextMacroScope_2132_);
lean_inc(v_env_2131_);
lean_dec(v___x_2130_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2163_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = l_Lean_Environment_setExporting(v_env_2131_, v_isExporting_2124_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 5, v___x_2125_);
lean_ctor_set(v___x_2140_, 0, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_nextMacroScope_2132_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_ngen_2133_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_auxDeclNGen_2134_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_traceState_2135_);
lean_ctor_set(v_reuseFailAlloc_2162_, 5, v___x_2125_);
lean_ctor_set(v_reuseFailAlloc_2162_, 6, v_messages_2136_);
lean_ctor_set(v_reuseFailAlloc_2162_, 7, v_infoState_2137_);
lean_ctor_set(v_reuseFailAlloc_2162_, 8, v_snapshotTasks_2138_);
v___x_2144_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_mctx_2147_; lean_object* v_zetaDeltaFVarIds_2148_; lean_object* v_postponed_2149_; lean_object* v_diag_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2160_; 
v___x_2145_ = lean_st_ref_set(v___y_2123_, v___x_2144_);
v___x_2146_ = lean_st_ref_take(v___y_2126_);
v_mctx_2147_ = lean_ctor_get(v___x_2146_, 0);
v_zetaDeltaFVarIds_2148_ = lean_ctor_get(v___x_2146_, 2);
v_postponed_2149_ = lean_ctor_get(v___x_2146_, 3);
v_diag_2150_ = lean_ctor_get(v___x_2146_, 4);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2146_, 1);
lean_dec(v_unused_2161_);
v___x_2152_ = v___x_2146_;
v_isShared_2153_ = v_isSharedCheck_2160_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_diag_2150_);
lean_inc(v_postponed_2149_);
lean_inc(v_zetaDeltaFVarIds_2148_);
lean_inc(v_mctx_2147_);
lean_dec(v___x_2146_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2160_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v___x_2127_);
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_mctx_2147_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_zetaDeltaFVarIds_2148_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_postponed_2149_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_diag_2150_);
v___x_2155_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_st_ref_set(v___y_2126_, v___x_2155_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0___boxed(lean_object* v___y_2165_, lean_object* v_isExporting_2166_, lean_object* v___x_2167_, lean_object* v___y_2168_, lean_object* v___x_2169_, lean_object* v_a_x3f_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v_isExporting_boxed_2172_; lean_object* v_res_2173_; 
v_isExporting_boxed_2172_ = lean_unbox(v_isExporting_2166_);
v_res_2173_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(v___y_2165_, v_isExporting_boxed_2172_, v___x_2167_, v___y_2168_, v___x_2169_, v_a_x3f_2170_);
lean_dec(v_a_x3f_2170_);
lean_dec(v___y_2168_);
lean_dec(v___y_2165_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(lean_object* v_x_2174_, uint8_t v_isExporting_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; lean_object* v_env_2184_; uint8_t v_isExporting_2185_; lean_object* v___x_2186_; lean_object* v_env_2187_; lean_object* v_nextMacroScope_2188_; lean_object* v_ngen_2189_; lean_object* v_auxDeclNGen_2190_; lean_object* v_traceState_2191_; lean_object* v_messages_2192_; lean_object* v_infoState_2193_; lean_object* v_snapshotTasks_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2248_; 
v___x_2183_ = lean_st_ref_get(v___y_2181_);
v_env_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc_ref(v_env_2184_);
lean_dec(v___x_2183_);
v_isExporting_2185_ = lean_ctor_get_uint8(v_env_2184_, sizeof(void*)*8);
lean_dec_ref(v_env_2184_);
v___x_2186_ = lean_st_ref_take(v___y_2181_);
v_env_2187_ = lean_ctor_get(v___x_2186_, 0);
v_nextMacroScope_2188_ = lean_ctor_get(v___x_2186_, 1);
v_ngen_2189_ = lean_ctor_get(v___x_2186_, 2);
v_auxDeclNGen_2190_ = lean_ctor_get(v___x_2186_, 3);
v_traceState_2191_ = lean_ctor_get(v___x_2186_, 4);
v_messages_2192_ = lean_ctor_get(v___x_2186_, 6);
v_infoState_2193_ = lean_ctor_get(v___x_2186_, 7);
v_snapshotTasks_2194_ = lean_ctor_get(v___x_2186_, 8);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v___x_2186_, 5);
lean_dec(v_unused_2249_);
v___x_2196_ = v___x_2186_;
v_isShared_2197_ = v_isSharedCheck_2248_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_snapshotTasks_2194_);
lean_inc(v_infoState_2193_);
lean_inc(v_messages_2192_);
lean_inc(v_traceState_2191_);
lean_inc(v_auxDeclNGen_2190_);
lean_inc(v_ngen_2189_);
lean_inc(v_nextMacroScope_2188_);
lean_inc(v_env_2187_);
lean_dec(v___x_2186_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2248_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2198_ = l_Lean_Environment_setExporting(v_env_2187_, v_isExporting_2175_);
v___x_2199_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 5, v___x_2199_);
lean_ctor_set(v___x_2196_, 0, v___x_2198_);
v___x_2201_ = v___x_2196_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_nextMacroScope_2188_);
lean_ctor_set(v_reuseFailAlloc_2247_, 2, v_ngen_2189_);
lean_ctor_set(v_reuseFailAlloc_2247_, 3, v_auxDeclNGen_2190_);
lean_ctor_set(v_reuseFailAlloc_2247_, 4, v_traceState_2191_);
lean_ctor_set(v_reuseFailAlloc_2247_, 5, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2247_, 6, v_messages_2192_);
lean_ctor_set(v_reuseFailAlloc_2247_, 7, v_infoState_2193_);
lean_ctor_set(v_reuseFailAlloc_2247_, 8, v_snapshotTasks_2194_);
v___x_2201_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_mctx_2204_; lean_object* v_zetaDeltaFVarIds_2205_; lean_object* v_postponed_2206_; lean_object* v_diag_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2245_; 
v___x_2202_ = lean_st_ref_set(v___y_2181_, v___x_2201_);
v___x_2203_ = lean_st_ref_take(v___y_2179_);
v_mctx_2204_ = lean_ctor_get(v___x_2203_, 0);
v_zetaDeltaFVarIds_2205_ = lean_ctor_get(v___x_2203_, 2);
v_postponed_2206_ = lean_ctor_get(v___x_2203_, 3);
v_diag_2207_ = lean_ctor_get(v___x_2203_, 4);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; 
v_unused_2246_ = lean_ctor_get(v___x_2203_, 1);
lean_dec(v_unused_2246_);
v___x_2209_ = v___x_2203_;
v_isShared_2210_ = v_isSharedCheck_2245_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_diag_2207_);
lean_inc(v_postponed_2206_);
lean_inc(v_zetaDeltaFVarIds_2205_);
lean_inc(v_mctx_2204_);
lean_dec(v___x_2203_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2245_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 1, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_mctx_2204_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v_zetaDeltaFVarIds_2205_);
lean_ctor_set(v_reuseFailAlloc_2244_, 3, v_postponed_2206_);
lean_ctor_set(v_reuseFailAlloc_2244_, 4, v_diag_2207_);
v___x_2213_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v_r_2215_; 
v___x_2214_ = lean_st_ref_set(v___y_2179_, v___x_2213_);
lean_inc(v___y_2181_);
lean_inc_ref(v___y_2180_);
lean_inc(v___y_2179_);
lean_inc_ref(v___y_2178_);
lean_inc(v___y_2177_);
lean_inc_ref(v___y_2176_);
v_r_2215_ = lean_apply_7(v_x_2174_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, lean_box(0));
if (lean_obj_tag(v_r_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2232_; 
v_a_2216_ = lean_ctor_get(v_r_2215_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_r_2215_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2218_ = v_r_2215_;
v_isShared_2219_ = v_isSharedCheck_2232_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v_r_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2232_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
lean_inc(v_a_2216_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set_tag(v___x_2218_, 1);
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
v___x_2222_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(v___y_2181_, v_isExporting_2185_, v___x_2199_, v___y_2179_, v___x_2211_, v___x_2221_);
lean_dec_ref(v___x_2221_);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; 
v_unused_2230_ = lean_ctor_get(v___x_2222_, 0);
lean_dec(v_unused_2230_);
v___x_2224_ = v___x_2222_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_dec(v___x_2222_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v_a_2216_);
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2216_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_a_2233_ = lean_ctor_get(v_r_2215_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v_r_2215_, 1);
v___x_2234_ = lean_box(0);
v___x_2235_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(v___y_2181_, v_isExporting_2185_, v___x_2199_, v___y_2179_, v___x_2211_, v___x_2234_);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v___x_2235_, 0);
lean_dec(v_unused_2243_);
v___x_2237_ = v___x_2235_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_dec(v___x_2235_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set_tag(v___x_2237_, 1);
lean_ctor_set(v___x_2237_, 0, v_a_2233_);
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2233_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___boxed(lean_object* v_x_2250_, lean_object* v_isExporting_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
uint8_t v_isExporting_boxed_2259_; lean_object* v_res_2260_; 
v_isExporting_boxed_2259_ = lean_unbox(v_isExporting_2251_);
v_res_2260_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(v_x_2250_, v_isExporting_boxed_2259_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(lean_object* v_x_2261_, uint8_t v_when_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
if (v_when_2262_ == 0)
{
lean_object* v___x_2270_; 
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2267_);
lean_inc(v___y_2266_);
lean_inc_ref(v___y_2265_);
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2263_);
v___x_2270_ = lean_apply_7(v_x_2261_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, lean_box(0));
return v___x_2270_;
}
else
{
uint8_t v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = 0;
v___x_2272_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(v_x_2261_, v___x_2271_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg___boxed(lean_object* v_x_2273_, lean_object* v_when_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v_when_boxed_2282_; lean_object* v_res_2283_; 
v_when_boxed_2282_ = lean_unbox(v_when_2274_);
v_res_2283_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(v_x_2273_, v_when_boxed_2282_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(lean_object* v_attrInstance_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___f_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___f_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; 
v___f_2293_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___closed__0));
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = l_Lean_Syntax_getArg(v_attrInstance_2285_, v___x_2295_);
v___x_2297_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2297_, 0, v___x_2296_);
v___f_2298_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___boxed), 12, 5);
lean_closure_set(v___f_2298_, 0, v___x_2297_);
lean_closure_set(v___f_2298_, 1, v_attrInstance_2285_);
lean_closure_set(v___f_2298_, 2, v___f_2293_);
lean_closure_set(v___f_2298_, 3, v___x_2294_);
lean_closure_set(v___f_2298_, 4, v___x_2295_);
v___x_2299_ = 1;
v___x_2300_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(v___f_2298_, v___x_2299_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___boxed(lean_object* v_attrInstance_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(v_attrInstance_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(lean_object* v_as_2310_, size_t v_sz_2311_, size_t v_i_2312_, lean_object* v_b_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_snd_2322_; uint8_t v___x_2326_; 
v___x_2326_ = lean_usize_dec_lt(v_i_2312_, v_sz_2311_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_b_2313_);
return v___x_2327_;
}
else
{
lean_object* v_fileName_2328_; lean_object* v_fileMap_2329_; lean_object* v_options_2330_; lean_object* v_currRecDepth_2331_; lean_object* v_maxRecDepth_2332_; lean_object* v_ref_2333_; lean_object* v_currNamespace_2334_; lean_object* v_openDecls_2335_; lean_object* v_initHeartbeats_2336_; lean_object* v_maxHeartbeats_2337_; lean_object* v_quotContext_2338_; lean_object* v_currMacroScope_2339_; uint8_t v_diag_2340_; lean_object* v_cancelTk_x3f_2341_; uint8_t v_suppressElabErrors_2342_; lean_object* v_inheritedTraceOptions_2343_; lean_object* v_a_2344_; lean_object* v_ref_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_fileName_2328_ = lean_ctor_get(v___y_2318_, 0);
v_fileMap_2329_ = lean_ctor_get(v___y_2318_, 1);
v_options_2330_ = lean_ctor_get(v___y_2318_, 2);
v_currRecDepth_2331_ = lean_ctor_get(v___y_2318_, 3);
v_maxRecDepth_2332_ = lean_ctor_get(v___y_2318_, 4);
v_ref_2333_ = lean_ctor_get(v___y_2318_, 5);
v_currNamespace_2334_ = lean_ctor_get(v___y_2318_, 6);
v_openDecls_2335_ = lean_ctor_get(v___y_2318_, 7);
v_initHeartbeats_2336_ = lean_ctor_get(v___y_2318_, 8);
v_maxHeartbeats_2337_ = lean_ctor_get(v___y_2318_, 9);
v_quotContext_2338_ = lean_ctor_get(v___y_2318_, 10);
v_currMacroScope_2339_ = lean_ctor_get(v___y_2318_, 11);
v_diag_2340_ = lean_ctor_get_uint8(v___y_2318_, sizeof(void*)*14);
v_cancelTk_x3f_2341_ = lean_ctor_get(v___y_2318_, 12);
v_suppressElabErrors_2342_ = lean_ctor_get_uint8(v___y_2318_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2343_ = lean_ctor_get(v___y_2318_, 13);
v_a_2344_ = lean_array_uget_borrowed(v_as_2310_, v_i_2312_);
v_ref_2345_ = l_Lean_replaceRef(v_a_2344_, v_ref_2333_);
lean_inc_ref(v_inheritedTraceOptions_2343_);
lean_inc(v_cancelTk_x3f_2341_);
lean_inc(v_currMacroScope_2339_);
lean_inc(v_quotContext_2338_);
lean_inc(v_maxHeartbeats_2337_);
lean_inc(v_initHeartbeats_2336_);
lean_inc(v_openDecls_2335_);
lean_inc(v_currNamespace_2334_);
lean_inc(v_maxRecDepth_2332_);
lean_inc(v_currRecDepth_2331_);
lean_inc_ref(v_options_2330_);
lean_inc_ref(v_fileMap_2329_);
lean_inc_ref(v_fileName_2328_);
v___x_2346_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2346_, 0, v_fileName_2328_);
lean_ctor_set(v___x_2346_, 1, v_fileMap_2329_);
lean_ctor_set(v___x_2346_, 2, v_options_2330_);
lean_ctor_set(v___x_2346_, 3, v_currRecDepth_2331_);
lean_ctor_set(v___x_2346_, 4, v_maxRecDepth_2332_);
lean_ctor_set(v___x_2346_, 5, v_ref_2345_);
lean_ctor_set(v___x_2346_, 6, v_currNamespace_2334_);
lean_ctor_set(v___x_2346_, 7, v_openDecls_2335_);
lean_ctor_set(v___x_2346_, 8, v_initHeartbeats_2336_);
lean_ctor_set(v___x_2346_, 9, v_maxHeartbeats_2337_);
lean_ctor_set(v___x_2346_, 10, v_quotContext_2338_);
lean_ctor_set(v___x_2346_, 11, v_currMacroScope_2339_);
lean_ctor_set(v___x_2346_, 12, v_cancelTk_x3f_2341_);
lean_ctor_set(v___x_2346_, 13, v_inheritedTraceOptions_2343_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*14, v_diag_2340_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*14 + 1, v_suppressElabErrors_2342_);
lean_inc(v_a_2344_);
v___x_2347_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(v_a_2344_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___x_2346_, v___y_2319_);
lean_dec_ref_known(v___x_2346_, 14);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = lean_array_push(v_b_2313_, v_a_2348_);
v_snd_2322_ = v___x_2349_;
goto v___jp_2321_;
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2370_; 
v_a_2350_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2352_ = v___x_2347_;
v_isShared_2353_ = v_isSharedCheck_2370_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2347_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2370_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
uint8_t v___y_2355_; uint8_t v___x_2368_; 
v___x_2368_ = l_Lean_Exception_isInterrupt(v_a_2350_);
if (v___x_2368_ == 0)
{
uint8_t v___x_2369_; 
lean_inc(v_a_2350_);
v___x_2369_ = l_Lean_Exception_isRuntime(v_a_2350_);
v___y_2355_ = v___x_2369_;
goto v___jp_2354_;
}
else
{
v___y_2355_ = v___x_2368_;
goto v___jp_2354_;
}
v___jp_2354_:
{
if (v___y_2355_ == 0)
{
lean_object* v___x_2356_; 
lean_del_object(v___x_2352_);
v___x_2356_ = l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32(v_a_2350_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_dec_ref_known(v___x_2356_, 1);
v_snd_2322_ = v_b_2313_;
goto v___jp_2321_;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v_b_2313_);
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v___x_2366_; 
lean_dec_ref(v_b_2313_);
if (v_isShared_2353_ == 0)
{
v___x_2366_ = v___x_2352_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2350_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
}
v___jp_2321_:
{
size_t v___x_2323_; size_t v___x_2324_; 
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_add(v_i_2312_, v___x_2323_);
v_i_2312_ = v___x_2324_;
v_b_2313_ = v_snd_2322_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33___boxed(lean_object* v_as_2371_, lean_object* v_sz_2372_, lean_object* v_i_2373_, lean_object* v_b_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
size_t v_sz_boxed_2382_; size_t v_i_boxed_2383_; lean_object* v_res_2384_; 
v_sz_boxed_2382_ = lean_unbox_usize(v_sz_2372_);
lean_dec(v_sz_2372_);
v_i_boxed_2383_ = lean_unbox_usize(v_i_2373_);
lean_dec(v_i_2373_);
v_res_2384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(v_as_2371_, v_sz_boxed_2382_, v_i_boxed_2383_, v_b_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec_ref(v_as_2371_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(lean_object* v_attrInstances_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_attrs_2395_; size_t v_sz_2396_; size_t v___x_2397_; lean_object* v___x_2398_; 
v_attrs_2395_ = ((lean_object*)(l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___closed__0));
v_sz_2396_ = lean_array_size(v_attrInstances_2387_);
v___x_2397_ = ((size_t)0ULL);
v___x_2398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(v_attrInstances_2387_, v_sz_2396_, v___x_2397_, v_attrs_2395_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___boxed(lean_object* v_attrInstances_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(v_attrInstances_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec_ref(v_attrInstances_2399_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(lean_object* v_stx_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = l_Lean_Syntax_getArg(v_stx_2408_, v___x_2416_);
v___x_2418_ = l_Lean_Syntax_getSepArgs(v___x_2417_);
lean_dec(v___x_2417_);
v___x_2419_ = l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(v___x_2418_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec_ref(v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9___boxed(lean_object* v_stx_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(v_stx_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v_stx_2420_);
return v_res_2428_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__0));
v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__2));
v___x_2434_ = l_Lean_stringToMessageData(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__4));
v___x_2437_ = l_Lean_stringToMessageData(v___x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5(lean_object* v_addInfo_2438_, lean_object* v_declName_2439_, uint8_t v___x_2440_, lean_object* v___f_2441_, uint8_t v___x_2442_, lean_object* v_env_2443_, lean_object* v___f_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; 
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v_declName_2439_);
v___x_2452_ = lean_apply_8(v_addInfo_2438_, v_declName_2439_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, lean_box(0));
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v___x_2453_; 
lean_dec_ref_known(v___x_2452_, 1);
lean_inc(v_declName_2439_);
v___x_2453_ = lean_private_to_user_name(v_declName_2439_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2454_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2455_ = l_Lean_MessageData_ofConstName(v_declName_2439_, v___x_2440_);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2454_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2458_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v___x_2459_;
}
else
{
lean_object* v_val_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_dec(v_declName_2439_);
v_val_2460_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_val_2460_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2461_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5);
v___x_2462_ = l_Lean_MessageData_ofConstName(v_val_2460_, v___x_2440_);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2465_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v___x_2466_;
}
}
else
{
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v_declName_2439_);
return v___x_2452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___boxed(lean_object* v_addInfo_2467_, lean_object* v_declName_2468_, lean_object* v___x_2469_, lean_object* v___f_2470_, lean_object* v___x_2471_, lean_object* v_env_2472_, lean_object* v___f_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v___x_56007__boxed_2481_; uint8_t v___x_56009__boxed_2482_; lean_object* v_res_2483_; 
v___x_56007__boxed_2481_ = lean_unbox(v___x_2469_);
v___x_56009__boxed_2482_ = lean_unbox(v___x_2471_);
v_res_2483_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5(v_addInfo_2467_, v_declName_2468_, v___x_56007__boxed_2481_, v___f_2470_, v___x_56009__boxed_2482_, v_env_2472_, v___f_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec_ref(v___f_2473_);
lean_dec_ref(v_env_2472_);
lean_dec_ref(v___f_2470_);
return v_res_2483_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__0));
v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3(lean_object* v___f_2487_, lean_object* v_declName_2488_, uint8_t v___x_2489_, lean_object* v_env_2490_, lean_object* v_____do__lift_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
uint8_t v___y_2500_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
lean_inc(v_declName_2488_);
v___x_2509_ = l_Lean_privateToUserName(v_declName_2488_);
lean_inc_ref(v_env_2490_);
v___x_2510_ = lean_is_reserved_name(v_env_2490_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; uint8_t v___x_2512_; 
lean_inc(v_declName_2488_);
v___x_2511_ = l_Lean_mkPrivateName(v_____do__lift_2491_, v_declName_2488_);
v___x_2512_ = lean_is_reserved_name(v_env_2490_, v___x_2511_);
v___y_2500_ = v___x_2512_;
goto v___jp_2499_;
}
else
{
lean_dec_ref(v_env_2490_);
v___y_2500_ = v___x_2510_;
goto v___jp_2499_;
}
v___jp_2499_:
{
if (v___y_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec(v_declName_2488_);
v___x_2501_ = lean_box(0);
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
v___x_2502_ = lean_apply_8(v___f_2487_, v___x_2501_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, lean_box(0));
return v___x_2502_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_dec_ref(v___f_2487_);
v___x_2503_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2504_ = l_Lean_MessageData_ofConstName(v_declName_2488_, v___x_2489_);
v___x_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1);
v___x_2507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2507_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___boxed(lean_object* v___f_2513_, lean_object* v_declName_2514_, lean_object* v___x_2515_, lean_object* v_env_2516_, lean_object* v_____do__lift_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
uint8_t v___x_56095__boxed_2525_; lean_object* v_res_2526_; 
v___x_56095__boxed_2525_ = lean_unbox(v___x_2515_);
v_res_2526_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3(v___f_2513_, v_declName_2514_, v___x_56095__boxed_2525_, v_env_2516_, v_____do__lift_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v_____do__lift_2517_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(lean_object* v_t_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; lean_object* v_infoState_2531_; uint8_t v_enabled_2532_; 
v___x_2530_ = lean_st_ref_get(v___y_2528_);
v_infoState_2531_ = lean_ctor_get(v___x_2530_, 7);
lean_inc_ref(v_infoState_2531_);
lean_dec(v___x_2530_);
v_enabled_2532_ = lean_ctor_get_uint8(v_infoState_2531_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2531_);
if (v_enabled_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec_ref(v_t_2527_);
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
return v___x_2534_;
}
else
{
lean_object* v___x_2535_; lean_object* v_infoState_2536_; lean_object* v_env_2537_; lean_object* v_nextMacroScope_2538_; lean_object* v_ngen_2539_; lean_object* v_auxDeclNGen_2540_; lean_object* v_traceState_2541_; lean_object* v_cache_2542_; lean_object* v_messages_2543_; lean_object* v_snapshotTasks_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2566_; 
v___x_2535_ = lean_st_ref_take(v___y_2528_);
v_infoState_2536_ = lean_ctor_get(v___x_2535_, 7);
v_env_2537_ = lean_ctor_get(v___x_2535_, 0);
v_nextMacroScope_2538_ = lean_ctor_get(v___x_2535_, 1);
v_ngen_2539_ = lean_ctor_get(v___x_2535_, 2);
v_auxDeclNGen_2540_ = lean_ctor_get(v___x_2535_, 3);
v_traceState_2541_ = lean_ctor_get(v___x_2535_, 4);
v_cache_2542_ = lean_ctor_get(v___x_2535_, 5);
v_messages_2543_ = lean_ctor_get(v___x_2535_, 6);
v_snapshotTasks_2544_ = lean_ctor_get(v___x_2535_, 8);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2546_ = v___x_2535_;
v_isShared_2547_ = v_isSharedCheck_2566_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_snapshotTasks_2544_);
lean_inc(v_infoState_2536_);
lean_inc(v_messages_2543_);
lean_inc(v_cache_2542_);
lean_inc(v_traceState_2541_);
lean_inc(v_auxDeclNGen_2540_);
lean_inc(v_ngen_2539_);
lean_inc(v_nextMacroScope_2538_);
lean_inc(v_env_2537_);
lean_dec(v___x_2535_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2566_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
uint8_t v_enabled_2548_; lean_object* v_assignment_2549_; lean_object* v_lazyAssignment_2550_; lean_object* v_trees_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2565_; 
v_enabled_2548_ = lean_ctor_get_uint8(v_infoState_2536_, sizeof(void*)*3);
v_assignment_2549_ = lean_ctor_get(v_infoState_2536_, 0);
v_lazyAssignment_2550_ = lean_ctor_get(v_infoState_2536_, 1);
v_trees_2551_ = lean_ctor_get(v_infoState_2536_, 2);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_infoState_2536_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2553_ = v_infoState_2536_;
v_isShared_2554_ = v_isSharedCheck_2565_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_trees_2551_);
lean_inc(v_lazyAssignment_2550_);
lean_inc(v_assignment_2549_);
lean_dec(v_infoState_2536_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2565_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = l_Lean_PersistentArray_push___redArg(v_trees_2551_, v_t_2527_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 2, v___x_2555_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_assignment_2549_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_lazyAssignment_2550_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v___x_2555_);
lean_ctor_set_uint8(v_reuseFailAlloc_2564_, sizeof(void*)*3, v_enabled_2548_);
v___x_2557_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 7, v___x_2557_);
v___x_2559_ = v___x_2546_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_env_2537_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_nextMacroScope_2538_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v_ngen_2539_);
lean_ctor_set(v_reuseFailAlloc_2563_, 3, v_auxDeclNGen_2540_);
lean_ctor_set(v_reuseFailAlloc_2563_, 4, v_traceState_2541_);
lean_ctor_set(v_reuseFailAlloc_2563_, 5, v_cache_2542_);
lean_ctor_set(v_reuseFailAlloc_2563_, 6, v_messages_2543_);
lean_ctor_set(v_reuseFailAlloc_2563_, 7, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2563_, 8, v_snapshotTasks_2544_);
v___x_2559_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = lean_st_ref_set(v___y_2528_, v___x_2559_);
v___x_2561_ = lean_box(0);
v___x_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
return v___x_2562_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_t_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v_t_2567_, v___y_2568_);
lean_dec(v___y_2568_);
return v_res_2570_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = lean_unsigned_to_nat(32u);
v___x_2572_ = lean_mk_empty_array_with_capacity(v___x_2571_);
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
return v___x_2573_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1(void){
_start:
{
size_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2574_ = ((size_t)5ULL);
v___x_2575_ = lean_unsigned_to_nat(0u);
v___x_2576_ = lean_unsigned_to_nat(32u);
v___x_2577_ = lean_mk_empty_array_with_capacity(v___x_2576_);
v___x_2578_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0);
v___x_2579_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v___x_2577_);
lean_ctor_set(v___x_2579_, 2, v___x_2575_);
lean_ctor_set(v___x_2579_, 3, v___x_2575_);
lean_ctor_set_usize(v___x_2579_, 4, v___x_2574_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(lean_object* v_t_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; lean_object* v_infoState_2589_; uint8_t v_enabled_2590_; 
v___x_2588_ = lean_st_ref_get(v___y_2586_);
v_infoState_2589_ = lean_ctor_get(v___x_2588_, 7);
lean_inc_ref(v_infoState_2589_);
lean_dec(v___x_2588_);
v_enabled_2590_ = lean_ctor_get_uint8(v_infoState_2589_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2589_);
if (v_enabled_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec_ref(v_t_2580_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1);
v___x_2594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2594_, 0, v_t_2580_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v___x_2594_, v___y_2586_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___boxed(lean_object* v_t_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(v_t_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__4(lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
if (lean_obj_tag(v_a_2605_) == 0)
{
lean_object* v___x_2607_; 
v___x_2607_ = l_List_reverse___redArg(v_a_2606_);
return v___x_2607_;
}
else
{
lean_object* v_head_2608_; lean_object* v_tail_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2618_; 
v_head_2608_ = lean_ctor_get(v_a_2605_, 0);
v_tail_2609_ = lean_ctor_get(v_a_2605_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_a_2605_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2611_ = v_a_2605_;
v_isShared_2612_ = v_isSharedCheck_2618_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_tail_2609_);
lean_inc(v_head_2608_);
lean_dec(v_a_2605_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2618_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2613_ = l_Lean_mkLevelParam(v_head_2608_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 1, v_a_2606_);
lean_ctor_set(v___x_2611_, 0, v___x_2613_);
v___x_2615_ = v___x_2611_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_a_2606_);
v___x_2615_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
v_a_2605_ = v_tail_2609_;
v_a_2606_ = v___x_2615_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0(void){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0);
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
return v___x_2621_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1);
v___x_2623_ = lean_unsigned_to_nat(0u);
v___x_2624_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
lean_ctor_set(v___x_2624_, 2, v___x_2623_);
lean_ctor_set(v___x_2624_, 3, v___x_2623_);
lean_ctor_set(v___x_2624_, 4, v___x_2622_);
lean_ctor_set(v___x_2624_, 5, v___x_2622_);
lean_ctor_set(v___x_2624_, 6, v___x_2622_);
lean_ctor_set(v___x_2624_, 7, v___x_2622_);
lean_ctor_set(v___x_2624_, 8, v___x_2622_);
lean_ctor_set(v___x_2624_, 9, v___x_2622_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = lean_unsigned_to_nat(32u);
v___x_2626_ = lean_mk_empty_array_with_capacity(v___x_2625_);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4(void){
_start:
{
size_t v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2628_ = ((size_t)5ULL);
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = lean_unsigned_to_nat(32u);
v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2630_);
v___x_2632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3);
v___x_2633_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v___x_2631_);
lean_ctor_set(v___x_2633_, 2, v___x_2629_);
lean_ctor_set(v___x_2633_, 3, v___x_2629_);
lean_ctor_set_usize(v___x_2633_, 4, v___x_2628_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2634_ = lean_box(1);
v___x_2635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4);
v___x_2636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1);
v___x_2637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
lean_ctor_set(v___x_2637_, 1, v___x_2635_);
lean_ctor_set(v___x_2637_, 2, v___x_2634_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__6));
v___x_2640_ = l_Lean_stringToMessageData(v___x_2639_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__8));
v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__10));
v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__12));
v___x_2649_ = l_Lean_stringToMessageData(v___x_2648_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__14));
v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__16));
v___x_2655_ = l_Lean_stringToMessageData(v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(lean_object* v_msg_2656_, lean_object* v_declHint_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; lean_object* v_env_2661_; uint8_t v___x_2662_; 
v___x_2660_ = lean_st_ref_get(v___y_2658_);
v_env_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc_ref(v_env_2661_);
lean_dec(v___x_2660_);
v___x_2662_ = l_Lean_Name_isAnonymous(v_declHint_2657_);
if (v___x_2662_ == 0)
{
uint8_t v_isExporting_2663_; 
v_isExporting_2663_ = lean_ctor_get_uint8(v_env_2661_, sizeof(void*)*8);
if (v_isExporting_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_dec_ref(v_env_2661_);
lean_dec(v_declHint_2657_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_msg_2656_);
return v___x_2664_;
}
else
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
lean_inc_ref(v_env_2661_);
v___x_2665_ = l_Lean_Environment_setExporting(v_env_2661_, v___x_2662_);
lean_inc(v_declHint_2657_);
lean_inc_ref(v___x_2665_);
v___x_2666_ = l_Lean_Environment_contains(v___x_2665_, v_declHint_2657_, v_isExporting_2663_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_dec_ref(v___x_2665_);
lean_dec_ref(v_env_2661_);
lean_dec(v_declHint_2657_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_msg_2656_);
return v___x_2667_;
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v_c_2673_; lean_object* v___x_2674_; 
v___x_2668_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2);
v___x_2669_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5);
v___x_2670_ = l_Lean_Options_empty;
v___x_2671_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2665_);
lean_ctor_set(v___x_2671_, 1, v___x_2668_);
lean_ctor_set(v___x_2671_, 2, v___x_2669_);
lean_ctor_set(v___x_2671_, 3, v___x_2670_);
lean_inc(v_declHint_2657_);
v___x_2672_ = l_Lean_MessageData_ofConstName(v_declHint_2657_, v___x_2662_);
v_c_2673_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2673_, 0, v___x_2671_);
lean_ctor_set(v_c_2673_, 1, v___x_2672_);
v___x_2674_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2661_, v_declHint_2657_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec_ref(v_env_2661_);
lean_dec(v_declHint_2657_);
v___x_2675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
lean_ctor_set(v___x_2676_, 1, v_c_2673_);
v___x_2677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_MessageData_note(v___x_2678_);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v_msg_2656_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
return v___x_2681_;
}
else
{
lean_object* v_val_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2717_; 
v_val_2682_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2684_ = v___x_2674_;
v_isShared_2685_ = v_isSharedCheck_2717_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_val_2682_);
lean_dec(v___x_2674_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2717_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v_mod_2689_; uint8_t v___x_2690_; 
v___x_2686_ = lean_box(0);
v___x_2687_ = l_Lean_Environment_header(v_env_2661_);
lean_dec_ref(v_env_2661_);
v___x_2688_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2687_);
v_mod_2689_ = lean_array_get(v___x_2686_, v___x_2688_, v_val_2682_);
lean_dec(v_val_2682_);
lean_dec_ref(v___x_2688_);
v___x_2690_ = l_Lean_isPrivateName(v_declHint_2657_);
lean_dec(v_declHint_2657_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2691_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
lean_ctor_set(v___x_2692_, 1, v_c_2673_);
v___x_2693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = l_Lean_MessageData_ofName(v_mod_2689_);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2696_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = l_Lean_MessageData_note(v___x_2698_);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v_msg_2656_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2700_);
v___x_2702_ = v___x_2684_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2704_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v_c_2673_);
v___x_2706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = l_Lean_MessageData_ofName(v_mod_2689_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = l_Lean_MessageData_note(v___x_2711_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v_msg_2656_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2713_);
v___x_2715_ = v___x_2684_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2718_; 
lean_dec_ref(v_env_2661_);
lean_dec(v_declHint_2657_);
v___x_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2718_, 0, v_msg_2656_);
return v___x_2718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___boxed(lean_object* v_msg_2719_, lean_object* v_declHint_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(v_msg_2719_, v_declHint_2720_, v___y_2721_);
lean_dec(v___y_2721_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(lean_object* v_msg_2724_, lean_object* v_declHint_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2743_; 
v___x_2733_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(v_msg_2724_, v_declHint_2725_, v___y_2731_);
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2743_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2743_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2738_ = l_Lean_unknownIdentifierMessageTag;
v___x_2739_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
lean_ctor_set(v___x_2739_, 1, v_a_2734_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2739_);
v___x_2741_ = v___x_2736_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44___boxed(lean_object* v_msg_2744_, lean_object* v_declHint_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(v_msg_2744_, v_declHint_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(lean_object* v_ref_2754_, lean_object* v_msg_2755_, lean_object* v_declHint_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; lean_object* v_a_2765_; lean_object* v___x_2766_; 
v___x_2764_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(v_msg_2755_, v_declHint_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_ref_2754_, v_a_2765_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg___boxed(lean_object* v_ref_2767_, lean_object* v_msg_2768_, lean_object* v_declHint_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(v_ref_2767_, v_msg_2768_, v_declHint_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v_ref_2767_);
return v_res_2777_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__0));
v___x_2780_ = l_Lean_stringToMessageData(v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(lean_object* v_ref_2781_, lean_object* v_constName_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; uint8_t v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2790_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1);
v___x_2791_ = 0;
lean_inc(v_constName_2782_);
v___x_2792_ = l_Lean_MessageData_ofConstName(v_constName_2782_, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2790_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(v_ref_2781_, v___x_2795_, v_constName_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___boxed(lean_object* v_ref_2797_, lean_object* v_constName_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(v_ref_2797_, v_constName_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v_ref_2797_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(lean_object* v_constName_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_ref_2815_; lean_object* v___x_2816_; 
v_ref_2815_ = lean_ctor_get(v___y_2812_, 5);
v___x_2816_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(v_ref_2815_, v_constName_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg___boxed(lean_object* v_constName_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(v_constName_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(lean_object* v_constName_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; lean_object* v_env_2835_; uint8_t v___x_2836_; lean_object* v___x_2837_; 
v___x_2834_ = lean_st_ref_get(v___y_2832_);
v_env_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc_ref(v_env_2835_);
lean_dec(v___x_2834_);
v___x_2836_ = 0;
lean_inc(v_constName_2826_);
v___x_2837_ = l_Lean_Environment_findConstVal_x3f(v_env_2835_, v_constName_2826_, v___x_2836_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(v_constName_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
return v___x_2838_;
}
else
{
lean_object* v_val_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_constName_2826_);
v_val_2839_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2837_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_val_2839_);
lean_dec(v___x_2837_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 0);
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_val_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3___boxed(lean_object* v_constName_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(v_constName_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(lean_object* v_constName_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; 
lean_inc(v_constName_2856_);
v___x_2864_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(v_constName_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2876_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2876_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2876_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v_levelParams_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v_levelParams_2869_ = lean_ctor_get(v_a_2865_, 1);
lean_inc(v_levelParams_2869_);
lean_dec(v_a_2865_);
v___x_2870_ = lean_box(0);
v___x_2871_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__4(v_levelParams_2869_, v___x_2870_);
v___x_2872_ = l_Lean_mkConst(v_constName_2856_, v___x_2871_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2872_);
v___x_2874_ = v___x_2867_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec(v_constName_2856_);
v_a_2877_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2864_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2864_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1___boxed(lean_object* v_constName_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(v_constName_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2893_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2894_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0);
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2897_ = lean_box(1);
v___x_2898_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4);
v___x_2899_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1);
v___x_2900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2898_);
lean_ctor_set(v___x_2900_, 2, v___x_2897_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0(uint8_t v___x_2901_, lean_object* v_declName_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_ref_2910_; lean_object* v___x_2911_; 
v_ref_2910_ = lean_ctor_get(v___y_2907_, 5);
v___x_2911_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(v_declName_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2911_, 1);
v___x_2913_ = lean_box(0);
lean_inc(v_ref_2910_);
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v_ref_2910_);
v___x_2915_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2);
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2917_, 0, v___x_2914_);
lean_ctor_set(v___x_2917_, 1, v___x_2915_);
lean_ctor_set(v___x_2917_, 2, v___x_2916_);
lean_ctor_set(v___x_2917_, 3, v_a_2912_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*4, v___x_2901_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*4 + 1, v___x_2901_);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
v___x_2919_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(v___x_2918_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
return v___x_2919_;
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
v_a_2920_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2911_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2911_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___boxed(lean_object* v___x_2928_, lean_object* v_declName_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
uint8_t v___x_56820__boxed_2937_; lean_object* v_res_2938_; 
v___x_56820__boxed_2937_ = lean_unbox(v___x_2928_);
v_res_2938_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0(v___x_56820__boxed_2937_, v_declName_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2938_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__0));
v___x_2941_ = l_Lean_stringToMessageData(v___x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2(lean_object* v_env_2942_, lean_object* v_declName_2943_, lean_object* v___f_2944_, lean_object* v_addInfo_2945_, lean_object* v_____r_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___x_2954_; uint8_t v___x_2955_; uint8_t v___x_2956_; 
lean_inc(v_declName_2943_);
v___x_2954_ = l_Lean_mkPrivateName(v_env_2942_, v_declName_2943_);
v___x_2955_ = 1;
lean_inc(v___x_2954_);
v___x_2956_ = l_Lean_Environment_contains(v_env_2942_, v___x_2954_, v___x_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_dec(v___x_2954_);
lean_dec_ref(v_addInfo_2945_);
lean_dec(v_declName_2943_);
v___x_2957_ = lean_box(0);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2951_);
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
v___x_2958_ = lean_apply_8(v___f_2944_, v___x_2957_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, lean_box(0));
return v___x_2958_;
}
else
{
lean_object* v___x_2959_; 
lean_dec_ref(v___f_2944_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2951_);
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
v___x_2959_ = lean_apply_8(v_addInfo_2945_, v___x_2954_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, lean_box(0));
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref_known(v___x_2959_, 1);
v___x_2960_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1);
v___x_2961_ = l_Lean_MessageData_ofConstName(v_declName_2943_, v___x_2955_);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2962_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2964_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
return v___x_2965_;
}
else
{
lean_dec(v_declName_2943_);
return v___x_2959_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___boxed(lean_object* v_env_2966_, lean_object* v_declName_2967_, lean_object* v___f_2968_, lean_object* v_addInfo_2969_, lean_object* v_____r_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2(v_env_2966_, v_declName_2967_, v___f_2968_, v_addInfo_2969_, v_____r_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4(lean_object* v___f_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; lean_object* v_env_2988_; lean_object* v___x_2989_; 
v___x_2987_ = lean_st_ref_get(v___y_2985_);
v_env_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc_ref(v_env_2988_);
lean_dec(v___x_2987_);
v___x_2989_ = lean_apply_8(v___f_2979_, v_env_2988_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, lean_box(0));
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4___boxed(lean_object* v___f_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4(v___f_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
return v_res_2998_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__0));
v___x_3001_ = l_Lean_stringToMessageData(v___x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1(lean_object* v_declName_3002_, lean_object* v_env_3003_, lean_object* v_addInfo_3004_, lean_object* v_____r_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_private_to_user_name(v_declName_3002_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_dec_ref(v_addInfo_3004_);
lean_dec_ref(v_env_3003_);
v___x_3014_ = lean_box(0);
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
return v___x_3015_;
}
else
{
lean_object* v_val_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3033_; 
v_val_3016_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3018_ = v___x_3013_;
v_isShared_3019_ = v_isSharedCheck_3033_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_val_3016_);
lean_dec(v___x_3013_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3033_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
uint8_t v___x_3020_; uint8_t v___x_3021_; 
v___x_3020_ = 1;
lean_inc(v_val_3016_);
v___x_3021_ = l_Lean_Environment_contains(v_env_3003_, v_val_3016_, v___x_3020_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
lean_dec(v_val_3016_);
lean_dec_ref(v_addInfo_3004_);
v___x_3022_ = lean_box(0);
if (v_isShared_3019_ == 0)
{
lean_ctor_set_tag(v___x_3018_, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3022_);
v___x_3024_ = v___x_3018_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
else
{
lean_object* v___x_3026_; 
lean_del_object(v___x_3018_);
lean_inc(v___y_3011_);
lean_inc_ref(v___y_3010_);
lean_inc(v___y_3009_);
lean_inc_ref(v___y_3008_);
lean_inc(v___y_3007_);
lean_inc_ref(v___y_3006_);
lean_inc(v_val_3016_);
v___x_3026_ = lean_apply_8(v_addInfo_3004_, v_val_3016_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, lean_box(0));
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
lean_dec_ref_known(v___x_3026_, 1);
v___x_3027_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1);
v___x_3028_ = l_Lean_MessageData_ofConstName(v_val_3016_, v___x_3020_);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_3031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3029_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_3031_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
return v___x_3032_;
}
else
{
lean_dec(v_val_3016_);
return v___x_3026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___boxed(lean_object* v_declName_3034_, lean_object* v_env_3035_, lean_object* v_addInfo_3036_, lean_object* v_____r_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1(v_declName_3034_, v_env_3035_, v_addInfo_3036_, v_____r_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(lean_object* v_env_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v_nextMacroScope_3051_; lean_object* v_ngen_3052_; lean_object* v_auxDeclNGen_3053_; lean_object* v_traceState_3054_; lean_object* v_messages_3055_; lean_object* v_infoState_3056_; lean_object* v_snapshotTasks_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3083_; 
v___x_3050_ = lean_st_ref_take(v___y_3048_);
v_nextMacroScope_3051_ = lean_ctor_get(v___x_3050_, 1);
v_ngen_3052_ = lean_ctor_get(v___x_3050_, 2);
v_auxDeclNGen_3053_ = lean_ctor_get(v___x_3050_, 3);
v_traceState_3054_ = lean_ctor_get(v___x_3050_, 4);
v_messages_3055_ = lean_ctor_get(v___x_3050_, 6);
v_infoState_3056_ = lean_ctor_get(v___x_3050_, 7);
v_snapshotTasks_3057_ = lean_ctor_get(v___x_3050_, 8);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3083_ == 0)
{
lean_object* v_unused_3084_; lean_object* v_unused_3085_; 
v_unused_3084_ = lean_ctor_get(v___x_3050_, 5);
lean_dec(v_unused_3084_);
v_unused_3085_ = lean_ctor_get(v___x_3050_, 0);
lean_dec(v_unused_3085_);
v___x_3059_ = v___x_3050_;
v_isShared_3060_ = v_isSharedCheck_3083_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_snapshotTasks_3057_);
lean_inc(v_infoState_3056_);
lean_inc(v_messages_3055_);
lean_inc(v_traceState_3054_);
lean_inc(v_auxDeclNGen_3053_);
lean_inc(v_ngen_3052_);
lean_inc(v_nextMacroScope_3051_);
lean_dec(v___x_3050_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3083_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3061_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 5, v___x_3061_);
lean_ctor_set(v___x_3059_, 0, v_env_3046_);
v___x_3063_ = v___x_3059_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_env_3046_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_nextMacroScope_3051_);
lean_ctor_set(v_reuseFailAlloc_3082_, 2, v_ngen_3052_);
lean_ctor_set(v_reuseFailAlloc_3082_, 3, v_auxDeclNGen_3053_);
lean_ctor_set(v_reuseFailAlloc_3082_, 4, v_traceState_3054_);
lean_ctor_set(v_reuseFailAlloc_3082_, 5, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3082_, 6, v_messages_3055_);
lean_ctor_set(v_reuseFailAlloc_3082_, 7, v_infoState_3056_);
lean_ctor_set(v_reuseFailAlloc_3082_, 8, v_snapshotTasks_3057_);
v___x_3063_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v_mctx_3066_; lean_object* v_zetaDeltaFVarIds_3067_; lean_object* v_postponed_3068_; lean_object* v_diag_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3080_; 
v___x_3064_ = lean_st_ref_set(v___y_3048_, v___x_3063_);
v___x_3065_ = lean_st_ref_take(v___y_3047_);
v_mctx_3066_ = lean_ctor_get(v___x_3065_, 0);
v_zetaDeltaFVarIds_3067_ = lean_ctor_get(v___x_3065_, 2);
v_postponed_3068_ = lean_ctor_get(v___x_3065_, 3);
v_diag_3069_ = lean_ctor_get(v___x_3065_, 4);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; 
v_unused_3081_ = lean_ctor_get(v___x_3065_, 1);
lean_dec(v_unused_3081_);
v___x_3071_ = v___x_3065_;
v_isShared_3072_ = v_isSharedCheck_3080_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_diag_3069_);
lean_inc(v_postponed_3068_);
lean_inc(v_zetaDeltaFVarIds_3067_);
lean_inc(v_mctx_3066_);
lean_dec(v___x_3065_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3080_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 1, v___x_3073_);
v___x_3075_ = v___x_3071_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_mctx_3066_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_zetaDeltaFVarIds_3067_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_postponed_3068_);
lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_diag_3069_);
v___x_3075_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_st_ref_set(v___y_3047_, v___x_3075_);
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
return v___x_3078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_env_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec(v___y_3087_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(lean_object* v_env_3091_, lean_object* v_x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; lean_object* v_env_3101_; lean_object* v_a_3103_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3100_ = lean_st_ref_get(v___y_3098_);
v_env_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc_ref(v_env_3101_);
lean_dec(v___x_3100_);
v___x_3113_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3091_, v___y_3096_, v___y_3098_);
lean_dec_ref(v___x_3113_);
lean_inc(v___y_3098_);
lean_inc_ref(v___y_3097_);
lean_inc(v___y_3096_);
lean_inc_ref(v___y_3095_);
lean_inc(v___y_3094_);
lean_inc_ref(v___y_3093_);
v___x_3114_ = lean_apply_7(v_x_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, lean_box(0));
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3101_, v___y_3096_, v___y_3098_);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; 
v_unused_3124_ = lean_ctor_get(v___x_3116_, 0);
lean_dec(v_unused_3124_);
v___x_3118_ = v___x_3116_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_dec(v___x_3116_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v_a_3115_);
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3115_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
else
{
lean_object* v_a_3125_; 
v_a_3125_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3125_);
lean_dec_ref_known(v___x_3114_, 1);
v_a_3103_ = v_a_3125_;
goto v___jp_3102_;
}
v___jp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
v___x_3104_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3101_, v___y_3096_, v___y_3098_);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v___x_3104_, 0);
lean_dec(v_unused_3112_);
v___x_3106_ = v___x_3104_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_dec(v___x_3104_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 1);
lean_ctor_set(v___x_3106_, 0, v_a_3103_);
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3103_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg___boxed(lean_object* v_env_3126_, lean_object* v_x_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3126_, v_x_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(lean_object* v_declName_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v___x_3147_; lean_object* v_env_3148_; uint8_t v___x_3149_; lean_object* v_addInfo_3150_; lean_object* v_env_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___x_3154_; lean_object* v___f_3155_; uint8_t v___x_3156_; uint8_t v___x_3157_; 
v___x_3147_ = lean_st_ref_get(v___y_3145_);
v_env_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc_ref(v_env_3148_);
lean_dec(v___x_3147_);
v___x_3149_ = 0;
v_addInfo_3150_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___closed__0));
v_env_3151_ = l_Lean_Environment_setExporting(v_env_3148_, v___x_3149_);
lean_inc_ref_n(v_env_3151_, 4);
lean_inc_n(v_declName_3139_, 4);
v___f_3152_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3152_, 0, v_declName_3139_);
lean_closure_set(v___f_3152_, 1, v_env_3151_);
lean_closure_set(v___f_3152_, 2, v_addInfo_3150_);
v___f_3153_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3153_, 0, v_env_3151_);
lean_closure_set(v___f_3153_, 1, v_declName_3139_);
lean_closure_set(v___f_3153_, 2, v___f_3152_);
lean_closure_set(v___f_3153_, 3, v_addInfo_3150_);
v___x_3154_ = lean_box(v___x_3149_);
lean_inc_ref(v___f_3153_);
v___f_3155_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___boxed), 12, 4);
lean_closure_set(v___f_3155_, 0, v___f_3153_);
lean_closure_set(v___f_3155_, 1, v_declName_3139_);
lean_closure_set(v___f_3155_, 2, v___x_3154_);
lean_closure_set(v___f_3155_, 3, v_env_3151_);
v___x_3156_ = 1;
v___x_3157_ = l_Lean_Environment_contains(v_env_3151_, v_declName_3139_, v___x_3156_);
if (v___x_3157_ == 0)
{
lean_object* v___f_3158_; lean_object* v___x_3159_; 
lean_dec_ref(v___f_3153_);
lean_dec(v_declName_3139_);
v___f_3158_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4___boxed), 8, 1);
lean_closure_set(v___f_3158_, 0, v___f_3155_);
v___x_3159_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3151_, v___f_3158_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
return v___x_3159_;
}
else
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___f_3162_; lean_object* v___x_3163_; 
v___x_3160_ = lean_box(v___x_3156_);
v___x_3161_ = lean_box(v___x_3149_);
lean_inc_ref(v_env_3151_);
v___f_3162_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___boxed), 14, 7);
lean_closure_set(v___f_3162_, 0, v_addInfo_3150_);
lean_closure_set(v___f_3162_, 1, v_declName_3139_);
lean_closure_set(v___f_3162_, 2, v___x_3160_);
lean_closure_set(v___f_3162_, 3, v___f_3153_);
lean_closure_set(v___f_3162_, 4, v___x_3161_);
lean_closure_set(v___f_3162_, 5, v_env_3151_);
lean_closure_set(v___f_3162_, 6, v___f_3155_);
v___x_3163_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3151_, v___f_3162_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___boxed(lean_object* v_declName_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(v_declName_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
return v_res_3172_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__1));
v___x_3177_ = l_Lean_MessageData_ofFormat(v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0(lean_object* v___x_3178_, uint8_t v___x_3179_, uint8_t v___x_3180_, lean_object* v_xs_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; 
lean_inc(v___x_3178_);
v___x_3189_ = l_Lean_Elab_Term_elabType(v___x_3178_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3189_, 1);
v___x_3191_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2);
v___x_3192_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_3190_, v___x_3178_, v___x_3191_, v___y_3183_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v___x_3193_; lean_object* v_fst_3194_; lean_object* v_snd_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref_known(v___x_3192_, 1);
v___x_3193_ = l_Array_unzip___redArg(v_xs_3181_);
v_fst_3194_ = lean_ctor_get(v___x_3193_, 0);
v_snd_3195_ = lean_ctor_get(v___x_3193_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3197_ = v___x_3193_;
v_isShared_3198_ = v_isSharedCheck_3220_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_snd_3195_);
lean_inc(v_fst_3194_);
lean_dec(v___x_3193_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3220_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
uint8_t v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = 1;
v___x_3200_ = l_Lean_Meta_mkForallFVars(v_snd_3195_, v_a_3190_, v___x_3179_, v___x_3180_, v___x_3180_, v___x_3199_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v_snd_3195_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3211_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3211_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3211_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 1, v_fst_3194_);
lean_ctor_set(v___x_3197_, 0, v_a_3201_);
v___x_3206_ = v___x_3197_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3201_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_fst_3194_);
v___x_3206_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3208_; 
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3206_);
v___x_3208_ = v___x_3203_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3206_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_del_object(v___x_3197_);
lean_dec(v_fst_3194_);
v_a_3212_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3200_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3200_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_a_3190_);
v_a_3221_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3192_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3192_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v___x_3178_);
v_a_3229_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3189_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3189_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___boxed(lean_object* v___x_3237_, lean_object* v___x_3238_, lean_object* v___x_3239_, lean_object* v_xs_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
uint8_t v___x_57276__boxed_3248_; uint8_t v___x_57277__boxed_3249_; lean_object* v_res_3250_; 
v___x_57276__boxed_3248_ = lean_unbox(v___x_3238_);
v___x_57277__boxed_3249_ = lean_unbox(v___x_3239_);
v_res_3250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0(v___x_3237_, v___x_57276__boxed_3248_, v___x_57277__boxed_3249_, v_xs_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec_ref(v_xs_3240_);
return v_res_3250_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(lean_object* v_declName_3251_, lean_object* v_as_3252_, size_t v_i_3253_, size_t v_stop_3254_){
_start:
{
uint8_t v___x_3255_; 
v___x_3255_ = lean_usize_dec_eq(v_i_3253_, v_stop_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v_declName_3257_; uint8_t v___x_3258_; 
v___x_3256_ = lean_array_uget_borrowed(v_as_3252_, v_i_3253_);
v_declName_3257_ = lean_ctor_get(v___x_3256_, 3);
v___x_3258_ = lean_name_eq(v_declName_3257_, v_declName_3251_);
if (v___x_3258_ == 0)
{
size_t v___x_3259_; size_t v___x_3260_; 
v___x_3259_ = ((size_t)1ULL);
v___x_3260_ = lean_usize_add(v_i_3253_, v___x_3259_);
v_i_3253_ = v___x_3260_;
goto _start;
}
else
{
return v___x_3258_;
}
}
else
{
uint8_t v___x_3262_; 
v___x_3262_ = 0;
return v___x_3262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6___boxed(lean_object* v_declName_3263_, lean_object* v_as_3264_, lean_object* v_i_3265_, lean_object* v_stop_3266_){
_start:
{
size_t v_i_boxed_3267_; size_t v_stop_boxed_3268_; uint8_t v_res_3269_; lean_object* v_r_3270_; 
v_i_boxed_3267_ = lean_unbox_usize(v_i_3265_);
lean_dec(v_i_3265_);
v_stop_boxed_3268_ = lean_unbox_usize(v_stop_3266_);
lean_dec(v_stop_3266_);
v_res_3269_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(v_declName_3263_, v_as_3264_, v_i_boxed_3267_, v_stop_boxed_3268_);
lean_dec_ref(v_as_3264_);
lean_dec(v_declName_3263_);
v_r_3270_ = lean_box(v_res_3269_);
return v_r_3270_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__0));
v___x_3273_ = l_Lean_stringToMessageData(v___x_3272_);
return v___x_3273_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__8));
v___x_3294_ = l_Lean_stringToMessageData(v___x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(uint8_t v___x_3295_, lean_object* v_as_3296_, size_t v_sz_3297_, size_t v_i_3298_, lean_object* v_b_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_a_3308_; uint8_t v___x_3312_; 
v___x_3312_ = lean_usize_dec_lt(v_i_3298_, v_sz_3297_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v_b_3299_);
return v___x_3313_;
}
else
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v_a_3316_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v_valStx_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; uint8_t v___y_3350_; uint8_t v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; uint8_t v___y_3444_; uint8_t v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; uint8_t v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; uint8_t v___y_3461_; uint8_t v___y_3495_; lean_object* v___y_3496_; uint8_t v___y_3497_; lean_object* v___y_3498_; uint8_t v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v_declName_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; uint8_t v___y_3518_; lean_object* v___y_3519_; uint8_t v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; uint8_t v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; uint8_t v___y_3538_; lean_object* v___y_3539_; uint8_t v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; uint8_t v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; uint8_t v___y_3562_; uint8_t v___y_3563_; lean_object* v___y_3564_; uint8_t v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; uint8_t v___y_3590_; uint8_t v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; uint8_t v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3617_; lean_object* v_attrs_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3654_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3314_ = lean_unsigned_to_nat(0u);
v___x_3315_ = lean_unsigned_to_nat(1u);
v_a_3316_ = lean_array_uget_borrowed(v_as_3296_, v_i_3298_);
v___x_3669_ = l_Lean_Syntax_getArg(v_a_3316_, v___x_3314_);
v___x_3670_ = l_Lean_Syntax_getOptional_x3f(v___x_3669_);
lean_dec(v___x_3669_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_box(0);
v___y_3654_ = v___x_3671_;
goto v___jp_3653_;
}
else
{
lean_object* v_val_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3681_; 
v_val_3672_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3674_ = v___x_3670_;
v_isShared_3675_ = v_isSharedCheck_3681_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_val_3672_);
lean_dec(v___x_3670_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3681_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3676_ = lean_box(v___x_3295_);
v___x_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3677_, 0, v_val_3672_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v___x_3677_);
v___x_3679_ = v___x_3674_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
v___y_3654_ = v___x_3679_;
goto v___jp_3653_;
}
}
}
v___jp_3317_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = lean_unsigned_to_nat(3u);
v___x_3336_ = l_Lean_Syntax_getArg(v_a_3316_, v___x_3335_);
v___x_3337_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(v___x_3336_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3339_, 0, v___y_3324_);
lean_ctor_set(v___x_3339_, 1, v___y_3326_);
lean_ctor_set(v___x_3339_, 2, v___y_3318_);
lean_ctor_set(v___x_3339_, 3, v___y_3323_);
lean_ctor_set(v___x_3339_, 4, v___y_3322_);
lean_ctor_set(v___x_3339_, 5, v___y_3321_);
lean_ctor_set(v___x_3339_, 6, v___y_3320_);
lean_ctor_set(v___x_3339_, 7, v___y_3319_);
lean_ctor_set(v___x_3339_, 8, v___y_3325_);
lean_ctor_set(v___x_3339_, 9, v_valStx_3328_);
lean_ctor_set(v___x_3339_, 10, v_a_3338_);
lean_ctor_set(v___x_3339_, 11, v___y_3327_);
v___x_3340_ = lean_array_push(v_b_3299_, v___x_3339_);
v_a_3308_ = v___x_3340_;
goto v___jp_3307_;
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec(v_valStx_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v_b_3299_);
v_a_3341_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3337_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3337_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
v___jp_3349_:
{
lean_object* v___x_3366_; 
lean_inc(v___y_3356_);
v___x_3366_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(v___y_3356_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3366_) == 0)
{
uint8_t v___x_3367_; lean_object* v___x_3368_; 
lean_dec_ref_known(v___x_3366_, 1);
v___x_3367_ = 2;
lean_inc_ref(v___y_3357_);
lean_inc(v___y_3356_);
v___x_3368_ = l_Lean_Elab_Term_applyAttributesAt(v___y_3356_, v___y_3357_, v___x_3367_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v___x_3369_; 
lean_dec_ref_known(v___x_3368_, 1);
lean_inc(v___y_3356_);
v___x_3369_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(v___y_3356_, v___y_3352_, v___y_3355_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___f_3376_; lean_object* v___x_3377_; 
lean_dec_ref_known(v___x_3369_, 1);
v___x_3370_ = l_Lean_Syntax_getArg(v___y_3352_, v___x_3315_);
v___x_3371_ = l_Lean_Syntax_getArgs(v___x_3370_);
v___x_3372_ = l_Lean_Syntax_getArg(v___y_3352_, v___y_3359_);
v___x_3373_ = l_Lean_Elab_Term_expandOptType(v___y_3355_, v___x_3372_);
lean_dec(v___x_3372_);
v___x_3374_ = lean_box(v___y_3350_);
v___x_3375_ = lean_box(v___x_3312_);
v___f_3376_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3376_, 0, v___x_3373_);
lean_closure_set(v___f_3376_, 1, v___x_3374_);
lean_closure_set(v___f_3376_, 2, v___x_3375_);
v___x_3377_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___x_3371_, v___f_3376_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v_fst_3379_; lean_object* v_snd_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v_fst_3379_ = lean_ctor_get(v_a_3378_, 0);
lean_inc_n(v_fst_3379_, 2);
v_snd_3380_ = lean_ctor_get(v_a_3378_, 1);
lean_inc(v_snd_3380_);
lean_dec(v_a_3378_);
v___x_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_fst_3379_);
v___x_3382_ = 2;
v___x_3383_ = lean_box(0);
v___x_3384_ = l_Lean_Meta_mkFreshExprMVar(v___x_3381_, v___x_3382_, v___x_3383_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3384_) == 0)
{
if (v___y_3351_ == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = lean_unsigned_to_nat(3u);
v___x_3387_ = l_Lean_Syntax_getArg(v___y_3352_, v___x_3386_);
v___x_3388_ = lean_box(v___x_3312_);
v___x_3389_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed), 5, 3);
lean_closure_set(v___x_3389_, 0, v___y_3352_);
lean_closure_set(v___x_3389_, 1, v___x_3387_);
lean_closure_set(v___x_3389_, 2, v___x_3388_);
v___x_3390_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_3389_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v___y_3318_ = v___y_3353_;
v___y_3319_ = v_fst_3379_;
v___y_3320_ = v___x_3370_;
v___y_3321_ = v_snd_3380_;
v___y_3322_ = v___y_3354_;
v___y_3323_ = v___y_3356_;
v___y_3324_ = v___y_3355_;
v___y_3325_ = v_a_3385_;
v___y_3326_ = v___y_3357_;
v___y_3327_ = v___y_3358_;
v_valStx_3328_ = v_a_3391_;
v___y_3329_ = v___y_3360_;
v___y_3330_ = v___y_3361_;
v___y_3331_ = v___y_3362_;
v___y_3332_ = v___y_3363_;
v___y_3333_ = v___y_3364_;
v___y_3334_ = v___y_3365_;
goto v___jp_3317_;
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec(v_a_3385_);
lean_dec(v_snd_3380_);
lean_dec(v_fst_3379_);
lean_dec(v___x_3370_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v_b_3299_);
v_a_3392_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3390_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3390_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v_a_3400_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3401_ = lean_unsigned_to_nat(4u);
v___x_3402_ = l_Lean_Syntax_getArg(v___y_3352_, v___x_3401_);
lean_dec(v___y_3352_);
v___y_3318_ = v___y_3353_;
v___y_3319_ = v_fst_3379_;
v___y_3320_ = v___x_3370_;
v___y_3321_ = v_snd_3380_;
v___y_3322_ = v___y_3354_;
v___y_3323_ = v___y_3356_;
v___y_3324_ = v___y_3355_;
v___y_3325_ = v_a_3400_;
v___y_3326_ = v___y_3357_;
v___y_3327_ = v___y_3358_;
v_valStx_3328_ = v___x_3402_;
v___y_3329_ = v___y_3360_;
v___y_3330_ = v___y_3361_;
v___y_3331_ = v___y_3362_;
v___y_3332_ = v___y_3363_;
v___y_3333_ = v___y_3364_;
v___y_3334_ = v___y_3365_;
goto v___jp_3317_;
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_snd_3380_);
lean_dec(v_fst_3379_);
lean_dec(v___x_3370_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v_b_3299_);
v_a_3403_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3384_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3384_);
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
lean_dec(v___x_3370_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v_b_3299_);
v_a_3411_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3377_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3377_);
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
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v_b_3299_);
v_a_3419_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3369_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3369_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v_b_3299_);
v_a_3427_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3368_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3368_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v_b_3299_);
v_a_3435_ = lean_ctor_get(v___x_3366_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3366_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3366_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
v___jp_3443_:
{
if (v___y_3461_ == 0)
{
v___y_3350_ = v___y_3444_;
v___y_3351_ = v___y_3452_;
v___y_3352_ = v___y_3453_;
v___y_3353_ = v___y_3454_;
v___y_3354_ = v___y_3456_;
v___y_3355_ = v___y_3457_;
v___y_3356_ = v___y_3458_;
v___y_3357_ = v___y_3447_;
v___y_3358_ = v___y_3449_;
v___y_3359_ = v___y_3448_;
v___y_3360_ = v___y_3459_;
v___y_3361_ = v___y_3450_;
v___y_3362_ = v___y_3455_;
v___y_3363_ = v___y_3446_;
v___y_3364_ = v___y_3460_;
v___y_3365_ = v___y_3451_;
goto v___jp_3349_;
}
else
{
lean_object* v_fileName_3462_; lean_object* v_fileMap_3463_; lean_object* v_options_3464_; lean_object* v_currRecDepth_3465_; lean_object* v_maxRecDepth_3466_; lean_object* v_ref_3467_; lean_object* v_currNamespace_3468_; lean_object* v_openDecls_3469_; lean_object* v_initHeartbeats_3470_; lean_object* v_maxHeartbeats_3471_; lean_object* v_quotContext_3472_; lean_object* v_currMacroScope_3473_; uint8_t v_diag_3474_; lean_object* v_cancelTk_x3f_3475_; uint8_t v_suppressElabErrors_3476_; lean_object* v_inheritedTraceOptions_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v_ref_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_fileName_3462_ = lean_ctor_get(v___y_3460_, 0);
v_fileMap_3463_ = lean_ctor_get(v___y_3460_, 1);
v_options_3464_ = lean_ctor_get(v___y_3460_, 2);
v_currRecDepth_3465_ = lean_ctor_get(v___y_3460_, 3);
v_maxRecDepth_3466_ = lean_ctor_get(v___y_3460_, 4);
v_ref_3467_ = lean_ctor_get(v___y_3460_, 5);
v_currNamespace_3468_ = lean_ctor_get(v___y_3460_, 6);
v_openDecls_3469_ = lean_ctor_get(v___y_3460_, 7);
v_initHeartbeats_3470_ = lean_ctor_get(v___y_3460_, 8);
v_maxHeartbeats_3471_ = lean_ctor_get(v___y_3460_, 9);
v_quotContext_3472_ = lean_ctor_get(v___y_3460_, 10);
v_currMacroScope_3473_ = lean_ctor_get(v___y_3460_, 11);
v_diag_3474_ = lean_ctor_get_uint8(v___y_3460_, sizeof(void*)*14);
v_cancelTk_x3f_3475_ = lean_ctor_get(v___y_3460_, 12);
v_suppressElabErrors_3476_ = lean_ctor_get_uint8(v___y_3460_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3477_ = lean_ctor_get(v___y_3460_, 13);
v___x_3478_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
lean_inc(v___y_3458_);
v___x_3479_ = l_Lean_MessageData_ofConstName(v___y_3458_, v___y_3445_);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_3482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v_ref_3483_ = l_Lean_replaceRef(v___y_3457_, v_ref_3467_);
lean_inc_ref(v_inheritedTraceOptions_3477_);
lean_inc(v_cancelTk_x3f_3475_);
lean_inc(v_currMacroScope_3473_);
lean_inc(v_quotContext_3472_);
lean_inc(v_maxHeartbeats_3471_);
lean_inc(v_initHeartbeats_3470_);
lean_inc(v_openDecls_3469_);
lean_inc(v_currNamespace_3468_);
lean_inc(v_maxRecDepth_3466_);
lean_inc(v_currRecDepth_3465_);
lean_inc_ref(v_options_3464_);
lean_inc_ref(v_fileMap_3463_);
lean_inc_ref(v_fileName_3462_);
v___x_3484_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3484_, 0, v_fileName_3462_);
lean_ctor_set(v___x_3484_, 1, v_fileMap_3463_);
lean_ctor_set(v___x_3484_, 2, v_options_3464_);
lean_ctor_set(v___x_3484_, 3, v_currRecDepth_3465_);
lean_ctor_set(v___x_3484_, 4, v_maxRecDepth_3466_);
lean_ctor_set(v___x_3484_, 5, v_ref_3483_);
lean_ctor_set(v___x_3484_, 6, v_currNamespace_3468_);
lean_ctor_set(v___x_3484_, 7, v_openDecls_3469_);
lean_ctor_set(v___x_3484_, 8, v_initHeartbeats_3470_);
lean_ctor_set(v___x_3484_, 9, v_maxHeartbeats_3471_);
lean_ctor_set(v___x_3484_, 10, v_quotContext_3472_);
lean_ctor_set(v___x_3484_, 11, v_currMacroScope_3473_);
lean_ctor_set(v___x_3484_, 12, v_cancelTk_x3f_3475_);
lean_ctor_set(v___x_3484_, 13, v_inheritedTraceOptions_3477_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*14, v_diag_3474_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*14 + 1, v_suppressElabErrors_3476_);
v___x_3485_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_3482_, v___y_3459_, v___y_3450_, v___y_3455_, v___y_3446_, v___x_3484_, v___y_3451_);
lean_dec_ref_known(v___x_3484_, 14);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_dec_ref_known(v___x_3485_, 1);
v___y_3350_ = v___y_3444_;
v___y_3351_ = v___y_3452_;
v___y_3352_ = v___y_3453_;
v___y_3353_ = v___y_3454_;
v___y_3354_ = v___y_3456_;
v___y_3355_ = v___y_3457_;
v___y_3356_ = v___y_3458_;
v___y_3357_ = v___y_3447_;
v___y_3358_ = v___y_3449_;
v___y_3359_ = v___y_3448_;
v___y_3360_ = v___y_3459_;
v___y_3361_ = v___y_3450_;
v___y_3362_ = v___y_3455_;
v___y_3363_ = v___y_3446_;
v___y_3364_ = v___y_3460_;
v___y_3365_ = v___y_3451_;
goto v___jp_3349_;
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3447_);
lean_dec_ref(v_b_3299_);
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
v___jp_3494_:
{
lean_object* v___x_3512_; uint8_t v___x_3513_; 
v___x_3512_ = lean_array_get_size(v_b_3299_);
v___x_3513_ = lean_nat_dec_lt(v___x_3314_, v___x_3512_);
if (v___x_3513_ == 0)
{
v___y_3444_ = v___y_3495_;
v___y_3445_ = v___y_3499_;
v___y_3446_ = v___y_3509_;
v___y_3447_ = v___y_3502_;
v___y_3448_ = v___y_3503_;
v___y_3449_ = v___y_3504_;
v___y_3450_ = v___y_3507_;
v___y_3451_ = v___y_3511_;
v___y_3452_ = v___y_3497_;
v___y_3453_ = v___y_3496_;
v___y_3454_ = v___y_3498_;
v___y_3455_ = v___y_3508_;
v___y_3456_ = v___y_3501_;
v___y_3457_ = v___y_3500_;
v___y_3458_ = v_declName_3505_;
v___y_3459_ = v___y_3506_;
v___y_3460_ = v___y_3510_;
v___y_3461_ = v___y_3499_;
goto v___jp_3443_;
}
else
{
if (v___x_3513_ == 0)
{
v___y_3444_ = v___y_3495_;
v___y_3445_ = v___y_3499_;
v___y_3446_ = v___y_3509_;
v___y_3447_ = v___y_3502_;
v___y_3448_ = v___y_3503_;
v___y_3449_ = v___y_3504_;
v___y_3450_ = v___y_3507_;
v___y_3451_ = v___y_3511_;
v___y_3452_ = v___y_3497_;
v___y_3453_ = v___y_3496_;
v___y_3454_ = v___y_3498_;
v___y_3455_ = v___y_3508_;
v___y_3456_ = v___y_3501_;
v___y_3457_ = v___y_3500_;
v___y_3458_ = v_declName_3505_;
v___y_3459_ = v___y_3506_;
v___y_3460_ = v___y_3510_;
v___y_3461_ = v___y_3499_;
goto v___jp_3443_;
}
else
{
size_t v___x_3514_; size_t v___x_3515_; uint8_t v___x_3516_; 
v___x_3514_ = ((size_t)0ULL);
v___x_3515_ = lean_usize_of_nat(v___x_3512_);
v___x_3516_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(v_declName_3505_, v_b_3299_, v___x_3514_, v___x_3515_);
v___y_3444_ = v___y_3495_;
v___y_3445_ = v___y_3499_;
v___y_3446_ = v___y_3509_;
v___y_3447_ = v___y_3502_;
v___y_3448_ = v___y_3503_;
v___y_3449_ = v___y_3504_;
v___y_3450_ = v___y_3507_;
v___y_3451_ = v___y_3511_;
v___y_3452_ = v___y_3497_;
v___y_3453_ = v___y_3496_;
v___y_3454_ = v___y_3498_;
v___y_3455_ = v___y_3508_;
v___y_3456_ = v___y_3501_;
v___y_3457_ = v___y_3500_;
v___y_3458_ = v_declName_3505_;
v___y_3459_ = v___y_3506_;
v___y_3460_ = v___y_3510_;
v___y_3461_ = v___x_3516_;
goto v___jp_3443_;
}
}
}
v___jp_3517_:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_mkPrivateName(v___y_3531_, v___y_3525_);
lean_dec_ref(v___y_3531_);
v___y_3495_ = v___y_3518_;
v___y_3496_ = v___y_3529_;
v___y_3497_ = v___y_3530_;
v___y_3498_ = v___y_3532_;
v___y_3499_ = v___y_3520_;
v___y_3500_ = v___y_3535_;
v___y_3501_ = v___y_3534_;
v___y_3502_ = v___y_3523_;
v___y_3503_ = v___y_3528_;
v___y_3504_ = v___y_3527_;
v_declName_3505_ = v___x_3536_;
v___y_3506_ = v___y_3533_;
v___y_3507_ = v___y_3526_;
v___y_3508_ = v___y_3524_;
v___y_3509_ = v___y_3522_;
v___y_3510_ = v___y_3521_;
v___y_3511_ = v___y_3519_;
goto v___jp_3494_;
}
v___jp_3537_:
{
lean_object* v___x_3555_; lean_object* v_env_3556_; lean_object* v___x_3557_; uint8_t v_isModule_3558_; lean_object* v___x_3559_; 
v___x_3555_ = lean_st_ref_get(v___y_3539_);
v_env_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc_ref(v_env_3556_);
lean_dec(v___x_3555_);
v___x_3557_ = l_Lean_Environment_header(v_env_3556_);
v_isModule_3558_ = lean_ctor_get_uint8(v___x_3557_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3557_);
lean_inc(v___y_3550_);
v___x_3559_ = l_Lean_Name_append(v___y_3554_, v___y_3550_);
if (v_isModule_3558_ == 0)
{
lean_dec_ref(v_env_3556_);
v___y_3495_ = v___y_3538_;
v___y_3496_ = v___y_3548_;
v___y_3497_ = v___y_3549_;
v___y_3498_ = v___y_3550_;
v___y_3499_ = v___y_3540_;
v___y_3500_ = v___y_3552_;
v___y_3501_ = v___y_3553_;
v___y_3502_ = v___y_3543_;
v___y_3503_ = v___y_3546_;
v___y_3504_ = v___y_3547_;
v_declName_3505_ = v___x_3559_;
v___y_3506_ = v___y_3551_;
v___y_3507_ = v___y_3545_;
v___y_3508_ = v___y_3544_;
v___y_3509_ = v___y_3542_;
v___y_3510_ = v___y_3541_;
v___y_3511_ = v___y_3539_;
goto v___jp_3494_;
}
else
{
uint8_t v_isExporting_3560_; 
v_isExporting_3560_ = lean_ctor_get_uint8(v_env_3556_, sizeof(void*)*8);
if (v_isExporting_3560_ == 0)
{
v___y_3518_ = v___y_3538_;
v___y_3519_ = v___y_3539_;
v___y_3520_ = v___y_3540_;
v___y_3521_ = v___y_3541_;
v___y_3522_ = v___y_3542_;
v___y_3523_ = v___y_3543_;
v___y_3524_ = v___y_3544_;
v___y_3525_ = v___x_3559_;
v___y_3526_ = v___y_3545_;
v___y_3527_ = v___y_3547_;
v___y_3528_ = v___y_3546_;
v___y_3529_ = v___y_3548_;
v___y_3530_ = v___y_3549_;
v___y_3531_ = v_env_3556_;
v___y_3532_ = v___y_3550_;
v___y_3533_ = v___y_3551_;
v___y_3534_ = v___y_3553_;
v___y_3535_ = v___y_3552_;
goto v___jp_3517_;
}
else
{
if (v___y_3540_ == 0)
{
lean_dec_ref(v_env_3556_);
v___y_3495_ = v___y_3538_;
v___y_3496_ = v___y_3548_;
v___y_3497_ = v___y_3549_;
v___y_3498_ = v___y_3550_;
v___y_3499_ = v___y_3540_;
v___y_3500_ = v___y_3552_;
v___y_3501_ = v___y_3553_;
v___y_3502_ = v___y_3543_;
v___y_3503_ = v___y_3546_;
v___y_3504_ = v___y_3547_;
v_declName_3505_ = v___x_3559_;
v___y_3506_ = v___y_3551_;
v___y_3507_ = v___y_3545_;
v___y_3508_ = v___y_3544_;
v___y_3509_ = v___y_3542_;
v___y_3510_ = v___y_3541_;
v___y_3511_ = v___y_3539_;
goto v___jp_3494_;
}
else
{
v___y_3518_ = v___y_3538_;
v___y_3519_ = v___y_3539_;
v___y_3520_ = v___y_3540_;
v___y_3521_ = v___y_3541_;
v___y_3522_ = v___y_3542_;
v___y_3523_ = v___y_3543_;
v___y_3524_ = v___y_3544_;
v___y_3525_ = v___x_3559_;
v___y_3526_ = v___y_3545_;
v___y_3527_ = v___y_3547_;
v___y_3528_ = v___y_3546_;
v___y_3529_ = v___y_3548_;
v___y_3530_ = v___y_3549_;
v___y_3531_ = v_env_3556_;
v___y_3532_ = v___y_3550_;
v___y_3533_ = v___y_3551_;
v___y_3534_ = v___y_3553_;
v___y_3535_ = v___y_3552_;
goto v___jp_3517_;
}
}
}
}
v___jp_3561_:
{
lean_object* v___x_3576_; 
v___x_3576_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v___y_3570_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3578_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3576_, 1);
v___x_3578_ = l_Lean_Syntax_getId(v___y_3566_);
if (lean_obj_tag(v_a_3577_) == 0)
{
lean_object* v___x_3579_; 
v___x_3579_ = lean_box(0);
v___y_3538_ = v___y_3562_;
v___y_3539_ = v___y_3575_;
v___y_3540_ = v___y_3565_;
v___y_3541_ = v___y_3574_;
v___y_3542_ = v___y_3573_;
v___y_3543_ = v___y_3567_;
v___y_3544_ = v___y_3572_;
v___y_3545_ = v___y_3571_;
v___y_3546_ = v___y_3569_;
v___y_3547_ = v___y_3568_;
v___y_3548_ = v___y_3564_;
v___y_3549_ = v___y_3563_;
v___y_3550_ = v___x_3578_;
v___y_3551_ = v___y_3570_;
v___y_3552_ = v___y_3566_;
v___y_3553_ = v_a_3577_;
v___y_3554_ = v___x_3579_;
goto v___jp_3537_;
}
else
{
lean_object* v_val_3580_; 
v_val_3580_ = lean_ctor_get(v_a_3577_, 0);
lean_inc(v_val_3580_);
v___y_3538_ = v___y_3562_;
v___y_3539_ = v___y_3575_;
v___y_3540_ = v___y_3565_;
v___y_3541_ = v___y_3574_;
v___y_3542_ = v___y_3573_;
v___y_3543_ = v___y_3567_;
v___y_3544_ = v___y_3572_;
v___y_3545_ = v___y_3571_;
v___y_3546_ = v___y_3569_;
v___y_3547_ = v___y_3568_;
v___y_3548_ = v___y_3564_;
v___y_3549_ = v___y_3563_;
v___y_3550_ = v___x_3578_;
v___y_3551_ = v___y_3570_;
v___y_3552_ = v___y_3566_;
v___y_3553_ = v_a_3577_;
v___y_3554_ = v_val_3580_;
goto v___jp_3537_;
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec(v___y_3564_);
lean_dec_ref(v_b_3299_);
v_a_3581_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3576_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3576_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
v___jp_3589_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3603_ = l_Lean_Syntax_getArg(v___y_3598_, v___x_3314_);
v___x_3604_ = l_Lean_Syntax_getArg(v___x_3603_, v___x_3314_);
lean_dec(v___x_3603_);
v___x_3605_ = l_Lean_Syntax_isIdent(v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1);
v___x_3607_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___x_3604_, v___x_3606_, v___y_3600_, v___y_3592_, v___y_3593_, v___y_3602_, v___y_3595_, v___y_3601_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_dec_ref_known(v___x_3607_, 1);
v___y_3562_ = v___y_3590_;
v___y_3563_ = v___y_3599_;
v___y_3564_ = v___y_3598_;
v___y_3565_ = v___y_3591_;
v___y_3566_ = v___x_3604_;
v___y_3567_ = v___y_3594_;
v___y_3568_ = v___y_3596_;
v___y_3569_ = v___y_3597_;
v___y_3570_ = v___y_3600_;
v___y_3571_ = v___y_3592_;
v___y_3572_ = v___y_3593_;
v___y_3573_ = v___y_3602_;
v___y_3574_ = v___y_3595_;
v___y_3575_ = v___y_3601_;
goto v___jp_3561_;
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec(v___x_3604_);
lean_dec(v___y_3598_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_b_3299_);
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3613_; 
if (v_isShared_3611_ == 0)
{
v___x_3613_ = v___x_3610_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v_a_3608_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
else
{
v___y_3562_ = v___y_3590_;
v___y_3563_ = v___y_3599_;
v___y_3564_ = v___y_3598_;
v___y_3565_ = v___y_3591_;
v___y_3566_ = v___x_3604_;
v___y_3567_ = v___y_3594_;
v___y_3568_ = v___y_3596_;
v___y_3569_ = v___y_3597_;
v___y_3570_ = v___y_3600_;
v___y_3571_ = v___y_3592_;
v___y_3572_ = v___y_3593_;
v___y_3573_ = v___y_3602_;
v___y_3574_ = v___y_3595_;
v___y_3575_ = v___y_3601_;
goto v___jp_3561_;
}
}
v___jp_3616_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; uint8_t v___x_3629_; 
v___x_3625_ = lean_unsigned_to_nat(2u);
v___x_3626_ = l_Lean_Syntax_getArg(v_a_3316_, v___x_3625_);
v___x_3627_ = l_Lean_Syntax_getArg(v___x_3626_, v___x_3314_);
lean_dec(v___x_3626_);
v___x_3628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3));
lean_inc(v___x_3627_);
v___x_3629_ = l_Lean_Syntax_isOfKind(v___x_3627_, v___x_3628_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5));
lean_inc(v___x_3627_);
v___x_3631_ = l_Lean_Syntax_isOfKind(v___x_3627_, v___x_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7));
lean_inc(v___x_3627_);
v___x_3633_ = l_Lean_Syntax_isOfKind(v___x_3627_, v___x_3632_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; 
lean_dec(v___x_3627_);
lean_dec_ref(v_attrs_3618_);
lean_dec(v___y_3617_);
v___x_3634_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_dec_ref_known(v___x_3634_, 1);
v_a_3308_ = v_b_3299_;
goto v___jp_3307_;
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v_b_3299_);
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
else
{
v___y_3590_ = v___x_3629_;
v___y_3591_ = v___x_3629_;
v___y_3592_ = v___y_3620_;
v___y_3593_ = v___y_3621_;
v___y_3594_ = v_attrs_3618_;
v___y_3595_ = v___y_3623_;
v___y_3596_ = v___y_3617_;
v___y_3597_ = v___x_3625_;
v___y_3598_ = v___x_3627_;
v___y_3599_ = v___x_3631_;
v___y_3600_ = v___y_3619_;
v___y_3601_ = v___y_3624_;
v___y_3602_ = v___y_3622_;
goto v___jp_3589_;
}
}
else
{
v___y_3590_ = v___x_3629_;
v___y_3591_ = v___x_3629_;
v___y_3592_ = v___y_3620_;
v___y_3593_ = v___y_3621_;
v___y_3594_ = v_attrs_3618_;
v___y_3595_ = v___y_3623_;
v___y_3596_ = v___y_3617_;
v___y_3597_ = v___x_3625_;
v___y_3598_ = v___x_3627_;
v___y_3599_ = v___x_3631_;
v___y_3600_ = v___y_3619_;
v___y_3601_ = v___y_3624_;
v___y_3602_ = v___y_3622_;
goto v___jp_3589_;
}
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_dec_ref(v_attrs_3618_);
lean_dec(v___y_3617_);
v___x_3643_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9);
v___x_3644_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___x_3627_, v___x_3643_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___x_3627_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_dec_ref_known(v___x_3644_, 1);
v_a_3308_ = v_b_3299_;
goto v___jp_3307_;
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec_ref(v_b_3299_);
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
v___jp_3653_:
{
lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3655_ = l_Lean_Syntax_getArg(v_a_3316_, v___x_3315_);
v___x_3656_ = l_Lean_Syntax_isNone(v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = l_Lean_Syntax_getArg(v___x_3655_, v___x_3314_);
lean_dec(v___x_3655_);
v___x_3658_ = l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(v___x_3657_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___x_3657_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref_known(v___x_3658_, 1);
v___y_3617_ = v___y_3654_;
v_attrs_3618_ = v_a_3659_;
v___y_3619_ = v___y_3300_;
v___y_3620_ = v___y_3301_;
v___y_3621_ = v___y_3302_;
v___y_3622_ = v___y_3303_;
v___y_3623_ = v___y_3304_;
v___y_3624_ = v___y_3305_;
goto v___jp_3616_;
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec(v___y_3654_);
lean_dec_ref(v_b_3299_);
v_a_3660_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3658_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3658_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v___x_3668_; 
lean_dec(v___x_3655_);
v___x_3668_ = ((lean_object*)(l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___closed__0));
v___y_3617_ = v___y_3654_;
v_attrs_3618_ = v___x_3668_;
v___y_3619_ = v___y_3300_;
v___y_3620_ = v___y_3301_;
v___y_3621_ = v___y_3302_;
v___y_3622_ = v___y_3303_;
v___y_3623_ = v___y_3304_;
v___y_3624_ = v___y_3305_;
goto v___jp_3616_;
}
}
}
v___jp_3307_:
{
size_t v___x_3309_; size_t v___x_3310_; 
v___x_3309_ = ((size_t)1ULL);
v___x_3310_ = lean_usize_add(v_i_3298_, v___x_3309_);
v_i_3298_ = v___x_3310_;
v_b_3299_ = v_a_3308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___boxed(lean_object* v___x_3682_, lean_object* v_as_3683_, lean_object* v_sz_3684_, lean_object* v_i_3685_, lean_object* v_b_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
uint8_t v___x_57487__boxed_3694_; size_t v_sz_boxed_3695_; size_t v_i_boxed_3696_; lean_object* v_res_3697_; 
v___x_57487__boxed_3694_ = lean_unbox(v___x_3682_);
v_sz_boxed_3695_ = lean_unbox_usize(v_sz_3684_);
lean_dec(v_sz_3684_);
v_i_boxed_3696_ = lean_unbox_usize(v_i_3685_);
lean_dec(v_i_3685_);
v_res_3697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(v___x_57487__boxed_3694_, v_as_3683_, v_sz_boxed_3695_, v_i_boxed_3696_, v_b_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v_as_3683_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(lean_object* v_letRec_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
lean_object* v_options_3708_; lean_object* v___x_3709_; lean_object* v_decls_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; size_t v_sz_3717_; size_t v___x_3718_; lean_object* v___x_3719_; 
v_options_3708_ = lean_ctor_get(v_a_3705_, 2);
v___x_3709_ = lean_unsigned_to_nat(0u);
v_decls_3710_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___closed__0));
v___x_3711_ = l_Lean_doc_verso;
v___x_3712_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_options_3708_, v___x_3711_);
v___x_3713_ = lean_unsigned_to_nat(1u);
v___x_3714_ = l_Lean_Syntax_getArg(v_letRec_3700_, v___x_3713_);
v___x_3715_ = l_Lean_Syntax_getArg(v___x_3714_, v___x_3709_);
lean_dec(v___x_3714_);
v___x_3716_ = l_Lean_Syntax_getSepArgs(v___x_3715_);
lean_dec(v___x_3715_);
v_sz_3717_ = lean_array_size(v___x_3716_);
v___x_3718_ = ((size_t)0ULL);
v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(v___x_3712_, v___x_3716_, v_sz_3717_, v___x_3718_, v_decls_3710_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
lean_dec_ref(v___x_3716_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3730_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3730_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3730_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3728_; 
v___x_3724_ = lean_unsigned_to_nat(3u);
v___x_3725_ = l_Lean_Syntax_getArg(v_letRec_3700_, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v_a_3720_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3726_);
v___x_3728_ = v___x_3722_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3719_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3719_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___boxed(lean_object* v_letRec_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(v_letRec_3739_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3743_);
lean_dec_ref(v_a_3742_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
lean_dec(v_letRec_3739_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5(lean_object* v_stx_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_stx_3748_, v___y_3753_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___boxed(lean_object* v_stx_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5(v_stx_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v_stx_3757_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6(lean_object* v_declName_3766_, lean_object* v_declRanges_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_3766_, v_declRanges_3767_, v___y_3771_, v___y_3773_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___boxed(lean_object* v_declName_3776_, lean_object* v_declRanges_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6(v_declName_3776_, v_declRanges_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(lean_object* v_00_u03b1_3786_, lean_object* v_x_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_x_3787_, v___y_3789_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___boxed(lean_object* v_00_u03b1_3791_, lean_object* v_x_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(v_00_u03b1_3791_, v_x_3792_, v___y_3793_, v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec_ref(v_x_3792_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(lean_object* v_00_u03b1_3796_, lean_object* v_ref_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(v_ref_3797_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___boxed(lean_object* v_00_u03b1_3806_, lean_object* v_ref_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(v_00_u03b1_3806_, v_ref_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4(lean_object* v_00_u03b1_3816_, lean_object* v_x_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v_x_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___boxed(lean_object* v_00_u03b1_3826_, lean_object* v_x_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4(v_00_u03b1_3826_, v_x_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5(lean_object* v_00_u03b1_3836_, lean_object* v_msg_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v_msg_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___boxed(lean_object* v_00_u03b1_3846_, lean_object* v_msg_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5(v_00_u03b1_3846_, v_msg_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6(lean_object* v_t_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v_t_3856_, v___y_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___boxed(lean_object* v_t_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6(v_t_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8(lean_object* v_env_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3874_, v___y_3878_, v___y_3880_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___boxed(lean_object* v_env_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8(v_env_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3(lean_object* v_00_u03b1_3892_, lean_object* v_env_3893_, lean_object* v_x_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3893_, v_x_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3903_, lean_object* v_env_3904_, lean_object* v_x_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3(v_00_u03b1_3903_, v_env_3904_, v_x_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(lean_object* v_cls_3914_, lean_object* v_msg_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_3914_, v_msg_3915_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___boxed(lean_object* v_cls_3924_, lean_object* v_msg_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(v_cls_3924_, v_msg_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(lean_object* v_as_3934_, lean_object* v_as_x27_3935_, lean_object* v_b_3936_, lean_object* v_a_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(v_as_x27_3935_, v_b_3936_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___boxed(lean_object* v_as_3946_, lean_object* v_as_x27_3947_, lean_object* v_b_3948_, lean_object* v_a_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(v_as_3946_, v_as_x27_3947_, v_b_3948_, v_a_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v_as_x27_3947_);
lean_dec(v_as_3946_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(lean_object* v_msgData_3958_, lean_object* v_macroStack_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg(v_msgData_3958_, v_macroStack_3959_, v___y_3964_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___boxed(lean_object* v_msgData_3968_, lean_object* v_macroStack_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(v_msgData_3968_, v_macroStack_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19(lean_object* v_00_u03b2_3978_, lean_object* v_m_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(v_m_3979_, v_a_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___boxed(lean_object* v_00_u03b2_3982_, lean_object* v_m_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19(v_00_u03b2_3982_, v_m_3983_, v_a_3984_);
lean_dec(v_a_3984_);
lean_dec_ref(v_m_3983_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17(lean_object* v_00_u03b1_3986_, lean_object* v_constName_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(v_constName_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___boxed(lean_object* v_00_u03b1_3996_, lean_object* v_constName_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17(v_00_u03b1_3996_, v_constName_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
return v_res_4005_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26(lean_object* v_00_u03b2_4006_, lean_object* v_x_4007_, lean_object* v_x_4008_){
_start:
{
uint8_t v___x_4009_; 
v___x_4009_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(v_x_4007_, v_x_4008_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___boxed(lean_object* v_00_u03b2_4010_, lean_object* v_x_4011_, lean_object* v_x_4012_){
_start:
{
uint8_t v_res_4013_; lean_object* v_r_4014_; 
v_res_4013_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26(v_00_u03b2_4010_, v_x_4011_, v_x_4012_);
lean_dec_ref(v_x_4012_);
lean_dec_ref(v_x_4011_);
v_r_4014_ = lean_box(v_res_4013_);
return v_r_4014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29(lean_object* v_00_u03b2_4015_, lean_object* v_a_4016_, lean_object* v_x_4017_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(v_a_4016_, v_x_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___boxed(lean_object* v_00_u03b2_4019_, lean_object* v_a_4020_, lean_object* v_x_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29(v_00_u03b2_4019_, v_a_4020_, v_x_4021_);
lean_dec(v_x_4021_);
lean_dec(v_a_4020_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39(lean_object* v_00_u03b1_4023_, lean_object* v_x_4024_, uint8_t v_isExporting_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(v_x_4024_, v_isExporting_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___boxed(lean_object* v_00_u03b1_4034_, lean_object* v_x_4035_, lean_object* v_isExporting_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
uint8_t v_isExporting_boxed_4044_; lean_object* v_res_4045_; 
v_isExporting_boxed_4044_ = lean_unbox(v_isExporting_4036_);
v_res_4045_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39(v_00_u03b1_4034_, v_x_4035_, v_isExporting_boxed_4044_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36(lean_object* v_00_u03b1_4046_, lean_object* v_x_4047_, uint8_t v_when_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(v_x_4047_, v_when_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___boxed(lean_object* v_00_u03b1_4057_, lean_object* v_x_4058_, lean_object* v_when_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
uint8_t v_when_boxed_4067_; lean_object* v_res_4068_; 
v_when_boxed_4067_ = lean_unbox(v_when_4059_);
v_res_4068_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36(v_00_u03b1_4057_, v_x_4058_, v_when_boxed_4067_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28(lean_object* v_00_u03b1_4069_, lean_object* v_ref_4070_, lean_object* v_constName_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(v_ref_4070_, v_constName_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___boxed(lean_object* v_00_u03b1_4080_, lean_object* v_ref_4081_, lean_object* v_constName_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28(v_00_u03b1_4080_, v_ref_4081_, v_constName_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v_ref_4081_);
return v_res_4090_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32(lean_object* v_00_u03b2_4091_, lean_object* v_x_4092_, size_t v_x_4093_, lean_object* v_x_4094_){
_start:
{
uint8_t v___x_4095_; 
v___x_4095_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(v_x_4092_, v_x_4093_, v_x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4096_, lean_object* v_x_4097_, lean_object* v_x_4098_, lean_object* v_x_4099_){
_start:
{
size_t v_x_58681__boxed_4100_; uint8_t v_res_4101_; lean_object* v_r_4102_; 
v_x_58681__boxed_4100_ = lean_unbox_usize(v_x_4098_);
lean_dec(v_x_4098_);
v_res_4101_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32(v_00_u03b2_4096_, v_x_4097_, v_x_58681__boxed_4100_, v_x_4099_);
lean_dec_ref(v_x_4099_);
lean_dec_ref(v_x_4097_);
v_r_4102_ = lean_box(v_res_4101_);
return v_r_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42(lean_object* v_ref_4103_, lean_object* v_msgData_4104_, uint8_t v_severity_4105_, uint8_t v_isSilent_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(v_ref_4103_, v_msgData_4104_, v_severity_4105_, v_isSilent_4106_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___boxed(lean_object* v_ref_4115_, lean_object* v_msgData_4116_, lean_object* v_severity_4117_, lean_object* v_isSilent_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
uint8_t v_severity_boxed_4126_; uint8_t v_isSilent_boxed_4127_; lean_object* v_res_4128_; 
v_severity_boxed_4126_ = lean_unbox(v_severity_4117_);
v_isSilent_boxed_4127_ = lean_unbox(v_isSilent_4118_);
v_res_4128_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42(v_ref_4115_, v_msgData_4116_, v_severity_boxed_4126_, v_isSilent_boxed_4127_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v_ref_4115_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37(lean_object* v_00_u03b1_4129_, lean_object* v_ref_4130_, lean_object* v_msg_4131_, lean_object* v_declHint_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(v_ref_4130_, v_msg_4131_, v_declHint_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___boxed(lean_object* v_00_u03b1_4141_, lean_object* v_ref_4142_, lean_object* v_msg_4143_, lean_object* v_declHint_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37(v_00_u03b1_4141_, v_ref_4142_, v_msg_4143_, v_declHint_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v_ref_4142_);
return v_res_4152_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40(lean_object* v_00_u03b2_4153_, lean_object* v_keys_4154_, lean_object* v_vals_4155_, lean_object* v_heq_4156_, lean_object* v_i_4157_, lean_object* v_k_4158_){
_start:
{
uint8_t v___x_4159_; 
v___x_4159_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(v_keys_4154_, v_i_4157_, v_k_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___boxed(lean_object* v_00_u03b2_4160_, lean_object* v_keys_4161_, lean_object* v_vals_4162_, lean_object* v_heq_4163_, lean_object* v_i_4164_, lean_object* v_k_4165_){
_start:
{
uint8_t v_res_4166_; lean_object* v_r_4167_; 
v_res_4166_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40(v_00_u03b2_4160_, v_keys_4161_, v_vals_4162_, v_heq_4163_, v_i_4164_, v_k_4165_);
lean_dec_ref(v_k_4165_);
lean_dec_ref(v_vals_4162_);
lean_dec_ref(v_keys_4161_);
v_r_4167_ = lean_box(v_res_4166_);
return v_r_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48(lean_object* v_msg_4168_, lean_object* v_declHint_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(v_msg_4168_, v_declHint_4169_, v___y_4175_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___boxed(lean_object* v_msg_4178_, lean_object* v_declHint_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48(v_msg_4178_, v_declHint_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0(lean_object* v_k_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v_b_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v___x_4197_; 
lean_inc(v___y_4195_);
lean_inc_ref(v___y_4194_);
lean_inc(v___y_4193_);
lean_inc_ref(v___y_4192_);
lean_inc(v___y_4190_);
lean_inc_ref(v___y_4189_);
v___x_4197_ = lean_apply_8(v_k_4188_, v_b_4191_, v___y_4189_, v___y_4190_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, lean_box(0));
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v_b_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0(v_k_4198_, v___y_4199_, v___y_4200_, v_b_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(lean_object* v_shortDeclName_4208_, lean_object* v_type_4209_, lean_object* v_declName_4210_, lean_object* v_k_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_){
_start:
{
lean_object* v___f_4219_; lean_object* v___x_4220_; 
lean_inc(v___y_4213_);
lean_inc_ref(v___y_4212_);
v___f_4219_ = lean_alloc_closure((void*)(l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4219_, 0, v_k_4211_);
lean_closure_set(v___f_4219_, 1, v___y_4212_);
lean_closure_set(v___f_4219_, 2, v___y_4213_);
v___x_4220_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withAuxDeclImp(lean_box(0), v_shortDeclName_4208_, v_type_4209_, v_declName_4210_, v___f_4219_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
if (lean_obj_tag(v___x_4220_) == 0)
{
return v___x_4220_;
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___boxed(lean_object* v_shortDeclName_4229_, lean_object* v_type_4230_, lean_object* v_declName_4231_, lean_object* v_k_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4229_, v_type_4230_, v_declName_4231_, v_k_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0(lean_object* v_00_u03b1_4241_, lean_object* v_shortDeclName_4242_, lean_object* v_type_4243_, lean_object* v_declName_4244_, lean_object* v_k_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4242_, v_type_4243_, v_declName_4244_, v_k_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___boxed(lean_object* v_00_u03b1_4254_, lean_object* v_shortDeclName_4255_, lean_object* v_type_4256_, lean_object* v_declName_4257_, lean_object* v_k_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0(v_00_u03b1_4254_, v_shortDeclName_4255_, v_type_4256_, v_declName_4257_, v_k_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0___boxed(lean_object* v_i_4267_, lean_object* v_fvars_4268_, lean_object* v_views_4269_, lean_object* v_k_4270_, lean_object* v_fvar_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0(v_i_4267_, v_fvars_4268_, v_views_4269_, v_k_4270_, v_fvar_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v_i_4267_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(lean_object* v_views_4280_, lean_object* v_k_4281_, lean_object* v_i_4282_, lean_object* v_fvars_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4291_ = lean_array_get_size(v_views_4280_);
v___x_4292_ = lean_nat_dec_lt(v_i_4282_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; 
lean_dec(v_i_4282_);
lean_dec_ref(v_views_4280_);
lean_inc(v_a_4289_);
lean_inc_ref(v_a_4288_);
lean_inc(v_a_4287_);
lean_inc_ref(v_a_4286_);
lean_inc(v_a_4285_);
lean_inc_ref(v_a_4284_);
v___x_4293_ = lean_apply_8(v_k_4281_, v_fvars_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, lean_box(0));
return v___x_4293_;
}
else
{
lean_object* v_view_4294_; lean_object* v_shortDeclName_4295_; lean_object* v_declName_4296_; lean_object* v_type_4297_; lean_object* v___f_4298_; lean_object* v___x_4299_; 
v_view_4294_ = lean_array_fget_borrowed(v_views_4280_, v_i_4282_);
v_shortDeclName_4295_ = lean_ctor_get(v_view_4294_, 2);
lean_inc(v_shortDeclName_4295_);
v_declName_4296_ = lean_ctor_get(v_view_4294_, 3);
lean_inc(v_declName_4296_);
v_type_4297_ = lean_ctor_get(v_view_4294_, 7);
lean_inc_ref(v_type_4297_);
v___f_4298_ = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4298_, 0, v_i_4282_);
lean_closure_set(v___f_4298_, 1, v_fvars_4283_);
lean_closure_set(v___f_4298_, 2, v_views_4280_);
lean_closure_set(v___f_4298_, 3, v_k_4281_);
v___x_4299_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4295_, v_type_4297_, v_declName_4296_, v___f_4298_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
return v___x_4299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0(lean_object* v_i_4300_, lean_object* v_fvars_4301_, lean_object* v_views_4302_, lean_object* v_k_4303_, lean_object* v_fvar_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4312_ = lean_unsigned_to_nat(1u);
v___x_4313_ = lean_nat_add(v_i_4300_, v___x_4312_);
v___x_4314_ = lean_array_push(v_fvars_4301_, v_fvar_4304_);
v___x_4315_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4302_, v_k_4303_, v___x_4313_, v___x_4314_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
return v___x_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___boxed(lean_object* v_views_4316_, lean_object* v_k_4317_, lean_object* v_i_4318_, lean_object* v_fvars_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4316_, v_k_4317_, v_i_4318_, v_fvars_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(lean_object* v_00_u03b1_4328_, lean_object* v_views_4329_, lean_object* v_k_4330_, lean_object* v_i_4331_, lean_object* v_fvars_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_){
_start:
{
lean_object* v___x_4340_; 
v___x_4340_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4329_, v_k_4330_, v_i_4331_, v_fvars_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___boxed(lean_object* v_00_u03b1_4341_, lean_object* v_views_4342_, lean_object* v_k_4343_, lean_object* v_i_4344_, lean_object* v_fvars_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(v_00_u03b1_4341_, v_views_4342_, v_k_4343_, v_i_4344_, v_fvars_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(lean_object* v_views_4356_, lean_object* v_k_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = lean_unsigned_to_nat(0u);
v___x_4366_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___closed__0));
v___x_4367_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4356_, v_k_4357_, v___x_4365_, v___x_4366_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___boxed(lean_object* v_views_4368_, lean_object* v_k_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_views_4368_, v_k_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
lean_dec(v_a_4375_);
lean_dec_ref(v_a_4374_);
lean_dec(v_a_4373_);
lean_dec_ref(v_a_4372_);
lean_dec(v_a_4371_);
lean_dec_ref(v_a_4370_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(lean_object* v_00_u03b1_4378_, lean_object* v_views_4379_, lean_object* v_k_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_views_4379_, v_k_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___boxed(lean_object* v_00_u03b1_4389_, lean_object* v_views_4390_, lean_object* v_k_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(v_00_u03b1_4389_, v_views_4390_, v_k_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
lean_dec(v_a_4397_);
lean_dec_ref(v_a_4396_);
lean_dec(v_a_4395_);
lean_dec_ref(v_a_4394_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0(lean_object* v_k_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v_b_4403_, lean_object* v_c_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v___x_4410_; 
lean_inc(v___y_4408_);
lean_inc_ref(v___y_4407_);
lean_inc(v___y_4406_);
lean_inc_ref(v___y_4405_);
lean_inc(v___y_4402_);
lean_inc_ref(v___y_4401_);
v___x_4410_ = lean_apply_9(v_k_4400_, v_b_4403_, v_c_4404_, v___y_4401_, v___y_4402_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, lean_box(0));
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0___boxed(lean_object* v_k_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v_b_4414_, lean_object* v_c_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0(v_k_4411_, v___y_4412_, v___y_4413_, v_b_4414_, v_c_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
return v_res_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(lean_object* v_type_4422_, lean_object* v_maxFVars_x3f_4423_, lean_object* v_k_4424_, uint8_t v_cleanupAnnotations_4425_, uint8_t v_whnfType_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___f_4434_; lean_object* v___x_4435_; 
lean_inc(v___y_4428_);
lean_inc_ref(v___y_4427_);
v___f_4434_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4434_, 0, v_k_4424_);
lean_closure_set(v___f_4434_, 1, v___y_4427_);
lean_closure_set(v___f_4434_, 2, v___y_4428_);
v___x_4435_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4422_, v_maxFVars_x3f_4423_, v___f_4434_, v_cleanupAnnotations_4425_, v_whnfType_4426_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
if (lean_obj_tag(v___x_4435_) == 0)
{
return v___x_4435_;
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___boxed(lean_object* v_type_4444_, lean_object* v_maxFVars_x3f_4445_, lean_object* v_k_4446_, lean_object* v_cleanupAnnotations_4447_, lean_object* v_whnfType_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4456_; uint8_t v_whnfType_boxed_4457_; lean_object* v_res_4458_; 
v_cleanupAnnotations_boxed_4456_ = lean_unbox(v_cleanupAnnotations_4447_);
v_whnfType_boxed_4457_ = lean_unbox(v_whnfType_4448_);
v_res_4458_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4444_, v_maxFVars_x3f_4445_, v_k_4446_, v_cleanupAnnotations_boxed_4456_, v_whnfType_boxed_4457_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1(lean_object* v_00_u03b1_4459_, lean_object* v_type_4460_, lean_object* v_maxFVars_x3f_4461_, lean_object* v_k_4462_, uint8_t v_cleanupAnnotations_4463_, uint8_t v_whnfType_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4460_, v_maxFVars_x3f_4461_, v_k_4462_, v_cleanupAnnotations_4463_, v_whnfType_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___boxed(lean_object* v_00_u03b1_4473_, lean_object* v_type_4474_, lean_object* v_maxFVars_x3f_4475_, lean_object* v_k_4476_, lean_object* v_cleanupAnnotations_4477_, lean_object* v_whnfType_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4486_; uint8_t v_whnfType_boxed_4487_; lean_object* v_res_4488_; 
v_cleanupAnnotations_boxed_4486_ = lean_unbox(v_cleanupAnnotations_4477_);
v_whnfType_boxed_4487_ = lean_unbox(v_whnfType_4478_);
v_res_4488_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1(v_00_u03b1_4473_, v_type_4474_, v_maxFVars_x3f_4475_, v_k_4476_, v_cleanupAnnotations_boxed_4486_, v_whnfType_boxed_4487_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0(lean_object* v_valStx_4489_, lean_object* v_x_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4498_, 0, v_x_4490_);
v___x_4499_ = l_Lean_Elab_Term_mkBodyInfo(v_valStx_4489_, v___x_4498_);
v___x_4500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
v___x_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0___boxed(lean_object* v_valStx_4502_, lean_object* v_x_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0(v_valStx_4502_, v_x_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(lean_object* v_upperBound_4512_, lean_object* v___x_4513_, lean_object* v_xs_4514_, lean_object* v_a_4515_, lean_object* v_b_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
uint8_t v___x_4524_; 
v___x_4524_ = lean_nat_dec_lt(v_a_4515_, v_upperBound_4512_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4525_; 
lean_dec(v_a_4515_);
v___x_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4525_, 0, v_b_4516_);
return v___x_4525_;
}
else
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4526_ = l_Lean_instInhabitedExpr;
v___x_4527_ = lean_array_fget_borrowed(v___x_4513_, v_a_4515_);
v___x_4528_ = lean_array_get_borrowed(v___x_4526_, v_xs_4514_, v_a_4515_);
lean_inc(v___x_4528_);
lean_inc(v___x_4527_);
v___x_4529_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_4527_, v___x_4528_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
lean_dec_ref_known(v___x_4529_, 1);
v___x_4530_ = lean_box(0);
v___x_4531_ = lean_unsigned_to_nat(1u);
v___x_4532_ = lean_nat_add(v_a_4515_, v___x_4531_);
lean_dec(v_a_4515_);
v_a_4515_ = v___x_4532_;
v_b_4516_ = v___x_4530_;
goto _start;
}
else
{
lean_dec(v_a_4515_);
return v___x_4529_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg___boxed(lean_object* v_upperBound_4534_, lean_object* v___x_4535_, lean_object* v_xs_4536_, lean_object* v_a_4537_, lean_object* v_b_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
lean_object* v_res_4546_; 
v_res_4546_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v_upperBound_4534_, v___x_4535_, v_xs_4536_, v_a_4537_, v_b_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec_ref(v_xs_4536_);
lean_dec_ref(v___x_4535_);
lean_dec(v_upperBound_4534_);
return v_res_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1(lean_object* v_valStx_4547_, lean_object* v___x_4548_, uint8_t v___x_4549_, lean_object* v___x_4550_, lean_object* v_xs_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v___x_4559_; 
v___x_4559_ = l_Lean_Elab_Term_elabTermEnsuringType(v_valStx_4547_, v___x_4548_, v___x_4549_, v___x_4549_, v___x_4550_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v_a_4560_; uint8_t v___x_4561_; uint8_t v___x_4562_; lean_object* v___x_4563_; 
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
lean_inc(v_a_4560_);
lean_dec_ref_known(v___x_4559_, 1);
v___x_4561_ = 0;
v___x_4562_ = 1;
v___x_4563_ = l_Lean_Meta_mkLambdaFVars(v_xs_4551_, v_a_4560_, v___x_4561_, v___x_4549_, v___x_4561_, v___x_4549_, v___x_4562_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4563_;
}
else
{
return v___x_4559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1___boxed(lean_object* v_valStx_4564_, lean_object* v___x_4565_, lean_object* v___x_4566_, lean_object* v___x_4567_, lean_object* v_xs_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
uint8_t v___x_3132__boxed_4576_; lean_object* v_res_4577_; 
v___x_3132__boxed_4576_ = lean_unbox(v___x_4566_);
v_res_4577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1(v_valStx_4564_, v___x_4565_, v___x_3132__boxed_4576_, v___x_4567_, v_xs_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4573_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v_xs_4568_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2(lean_object* v___x_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4578_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2___boxed(lean_object* v___x_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2(v___x_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3(lean_object* v___x_4596_, lean_object* v_binderIds_4597_, lean_object* v_valStx_4598_, uint8_t v___x_4599_, lean_object* v___f_4600_, lean_object* v_declName_4601_, lean_object* v_xs_4602_, lean_object* v_type_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4611_ = lean_unsigned_to_nat(0u);
v___x_4612_ = lean_box(0);
v___x_4613_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v___x_4596_, v_binderIds_4597_, v_xs_4602_, v___x_4611_, v___x_4612_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___f_4617_; lean_object* v___x_4618_; lean_object* v___f_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
lean_dec_ref_known(v___x_4613_, 1);
v___x_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4614_, 0, v_type_4603_);
v___x_4615_ = lean_box(0);
v___x_4616_ = lean_box(v___x_4599_);
lean_inc_n(v_valStx_4598_, 2);
v___f_4617_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4617_, 0, v_valStx_4598_);
lean_closure_set(v___f_4617_, 1, v___x_4614_);
lean_closure_set(v___f_4617_, 2, v___x_4616_);
lean_closure_set(v___f_4617_, 3, v___x_4615_);
lean_closure_set(v___f_4617_, 4, v_xs_4602_);
v___x_4618_ = l_Lean_Elab_Term_mkBodyInfo(v_valStx_4598_, v___x_4615_);
v___f_4619_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2___boxed), 8, 1);
lean_closure_set(v___f_4619_, 0, v___x_4618_);
v___x_4620_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withInfoContext_x27___boxed), 11, 4);
lean_closure_set(v___x_4620_, 0, v_valStx_4598_);
lean_closure_set(v___x_4620_, 1, v___f_4617_);
lean_closure_set(v___x_4620_, 2, v___f_4600_);
lean_closure_set(v___x_4620_, 3, v___f_4619_);
v___x_4621_ = l_Lean_Elab_Term_withDeclName___redArg(v_declName_4601_, v___x_4620_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
return v___x_4621_;
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
lean_dec_ref(v_type_4603_);
lean_dec_ref(v_xs_4602_);
lean_dec(v_declName_4601_);
lean_dec_ref(v___f_4600_);
lean_dec(v_valStx_4598_);
v_a_4622_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4613_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4613_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3___boxed(lean_object* v___x_4630_, lean_object* v_binderIds_4631_, lean_object* v_valStx_4632_, lean_object* v___x_4633_, lean_object* v___f_4634_, lean_object* v_declName_4635_, lean_object* v_xs_4636_, lean_object* v_type_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
uint8_t v___x_3199__boxed_4645_; lean_object* v_res_4646_; 
v___x_3199__boxed_4645_ = lean_unbox(v___x_4633_);
v_res_4646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3(v___x_4630_, v_binderIds_4631_, v_valStx_4632_, v___x_3199__boxed_4645_, v___f_4634_, v_declName_4635_, v_xs_4636_, v_type_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec_ref(v_binderIds_4631_);
lean_dec(v___x_4630_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(size_t v_sz_4647_, size_t v_i_4648_, lean_object* v_bs_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
uint8_t v___x_4657_; 
v___x_4657_ = lean_usize_dec_lt(v_i_4648_, v_sz_4647_);
if (v___x_4657_ == 0)
{
lean_object* v___x_4658_; 
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v_bs_4649_);
return v___x_4658_;
}
else
{
lean_object* v_v_4659_; lean_object* v_declName_4660_; lean_object* v_binderIds_4661_; lean_object* v_type_4662_; lean_object* v_valStx_4663_; lean_object* v___f_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___f_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; lean_object* v___x_4670_; 
v_v_4659_ = lean_array_uget_borrowed(v_bs_4649_, v_i_4648_);
v_declName_4660_ = lean_ctor_get(v_v_4659_, 3);
v_binderIds_4661_ = lean_ctor_get(v_v_4659_, 5);
v_type_4662_ = lean_ctor_get(v_v_4659_, 7);
v_valStx_4663_ = lean_ctor_get(v_v_4659_, 9);
lean_inc_n(v_valStx_4663_, 2);
v___f_4664_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4664_, 0, v_valStx_4663_);
v___x_4665_ = lean_array_get_size(v_binderIds_4661_);
v___x_4666_ = lean_box(v___x_4657_);
lean_inc(v_declName_4660_);
lean_inc_ref(v_binderIds_4661_);
v___f_4667_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3___boxed), 15, 6);
lean_closure_set(v___f_4667_, 0, v___x_4665_);
lean_closure_set(v___f_4667_, 1, v_binderIds_4661_);
lean_closure_set(v___f_4667_, 2, v_valStx_4663_);
lean_closure_set(v___f_4667_, 3, v___x_4666_);
lean_closure_set(v___f_4667_, 4, v___f_4664_);
lean_closure_set(v___f_4667_, 5, v_declName_4660_);
v___x_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4665_);
v___x_4669_ = 0;
lean_inc_ref(v_type_4662_);
v___x_4670_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4662_, v___x_4668_, v___f_4667_, v___x_4657_, v___x_4669_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4672_; lean_object* v_bs_x27_4673_; size_t v___x_4674_; size_t v___x_4675_; lean_object* v___x_4676_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v___x_4670_, 1);
v___x_4672_ = lean_unsigned_to_nat(0u);
v_bs_x27_4673_ = lean_array_uset(v_bs_4649_, v_i_4648_, v___x_4672_);
v___x_4674_ = ((size_t)1ULL);
v___x_4675_ = lean_usize_add(v_i_4648_, v___x_4674_);
v___x_4676_ = lean_array_uset(v_bs_x27_4673_, v_i_4648_, v_a_4671_);
v_i_4648_ = v___x_4675_;
v_bs_4649_ = v___x_4676_;
goto _start;
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
lean_dec_ref(v_bs_4649_);
v_a_4678_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4670_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4670_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___boxed(lean_object* v_sz_4686_, lean_object* v_i_4687_, lean_object* v_bs_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
size_t v_sz_boxed_4696_; size_t v_i_boxed_4697_; lean_object* v_res_4698_; 
v_sz_boxed_4696_ = lean_unbox_usize(v_sz_4686_);
lean_dec(v_sz_4686_);
v_i_boxed_4697_ = lean_unbox_usize(v_i_4687_);
lean_dec(v_i_4687_);
v_res_4698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(v_sz_boxed_4696_, v_i_boxed_4697_, v_bs_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(lean_object* v_view_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_decls_4707_; size_t v_sz_4708_; size_t v___x_4709_; lean_object* v___x_4710_; 
v_decls_4707_ = lean_ctor_get(v_view_4699_, 0);
lean_inc_ref(v_decls_4707_);
lean_dec_ref(v_view_4699_);
v_sz_4708_ = lean_array_size(v_decls_4707_);
v___x_4709_ = ((size_t)0ULL);
v___x_4710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(v_sz_4708_, v___x_4709_, v_decls_4707_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___boxed(lean_object* v_view_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(v_view_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_);
lean_dec(v_a_4717_);
lean_dec_ref(v_a_4716_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
lean_dec(v_a_4713_);
lean_dec_ref(v_a_4712_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0(lean_object* v_upperBound_4720_, lean_object* v___x_4721_, lean_object* v_xs_4722_, lean_object* v_inst_4723_, lean_object* v_R_4724_, lean_object* v_a_4725_, lean_object* v_b_4726_, lean_object* v_c_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_){
_start:
{
lean_object* v___x_4735_; 
v___x_4735_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v_upperBound_4720_, v___x_4721_, v_xs_4722_, v_a_4725_, v_b_4726_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
return v___x_4735_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___boxed(lean_object* v_upperBound_4736_, lean_object* v___x_4737_, lean_object* v_xs_4738_, lean_object* v_inst_4739_, lean_object* v_R_4740_, lean_object* v_a_4741_, lean_object* v_b_4742_, lean_object* v_c_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0(v_upperBound_4736_, v___x_4737_, v_xs_4738_, v_inst_4739_, v_R_4740_, v_a_4741_, v_b_4742_, v_c_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_);
lean_dec(v___y_4749_);
lean_dec_ref(v___y_4748_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec_ref(v_xs_4738_);
lean_dec_ref(v___x_4737_);
lean_dec(v_upperBound_4736_);
return v_res_4751_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(lean_object* v_a_4752_, lean_object* v_x_4753_){
_start:
{
if (lean_obj_tag(v_x_4753_) == 0)
{
uint8_t v___x_4754_; 
v___x_4754_ = 0;
return v___x_4754_;
}
else
{
lean_object* v_head_4755_; lean_object* v_tail_4756_; lean_object* v_declName_4757_; lean_object* v_declName_4758_; uint8_t v___x_4759_; 
v_head_4755_ = lean_ctor_get(v_x_4753_, 0);
v_tail_4756_ = lean_ctor_get(v_x_4753_, 1);
v_declName_4757_ = lean_ctor_get(v_head_4755_, 4);
v_declName_4758_ = lean_ctor_get(v_a_4752_, 3);
v___x_4759_ = lean_name_eq(v_declName_4757_, v_declName_4758_);
if (v___x_4759_ == 0)
{
v_x_4753_ = v_tail_4756_;
goto _start;
}
else
{
return v___x_4759_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___boxed(lean_object* v_a_4761_, lean_object* v_x_4762_){
_start:
{
uint8_t v_res_4763_; lean_object* v_r_4764_; 
v_res_4763_ = l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(v_a_4761_, v_x_4762_);
lean_dec(v_x_4762_);
lean_dec_ref(v_a_4761_);
v_r_4764_ = lean_box(v_res_4763_);
return v_r_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(lean_object* v___x_4765_, lean_object* v_as_4766_, size_t v_sz_4767_, size_t v_i_4768_, lean_object* v_b_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_){
_start:
{
lean_object* v_a_4778_; uint8_t v___x_4782_; 
v___x_4782_ = lean_usize_dec_lt(v_i_4768_, v_sz_4767_);
if (v___x_4782_ == 0)
{
lean_object* v___x_4783_; 
v___x_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4783_, 0, v_b_4769_);
return v___x_4783_;
}
else
{
lean_object* v___x_4784_; lean_object* v_a_4785_; uint8_t v___x_4786_; 
v___x_4784_ = lean_box(0);
v_a_4785_ = lean_array_uget_borrowed(v_as_4766_, v_i_4768_);
v___x_4786_ = l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(v_a_4785_, v___x_4765_);
if (v___x_4786_ == 0)
{
v_a_4778_ = v___x_4784_;
goto v___jp_4777_;
}
else
{
lean_object* v_ref_4787_; lean_object* v_declName_4788_; lean_object* v_fileName_4789_; lean_object* v_fileMap_4790_; lean_object* v_options_4791_; lean_object* v_currRecDepth_4792_; lean_object* v_maxRecDepth_4793_; lean_object* v_ref_4794_; lean_object* v_currNamespace_4795_; lean_object* v_openDecls_4796_; lean_object* v_initHeartbeats_4797_; lean_object* v_maxHeartbeats_4798_; lean_object* v_quotContext_4799_; lean_object* v_currMacroScope_4800_; uint8_t v_diag_4801_; lean_object* v_cancelTk_x3f_4802_; uint8_t v_suppressElabErrors_4803_; lean_object* v_inheritedTraceOptions_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v_ref_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v_ref_4787_ = lean_ctor_get(v_a_4785_, 0);
v_declName_4788_ = lean_ctor_get(v_a_4785_, 3);
v_fileName_4789_ = lean_ctor_get(v___y_4774_, 0);
v_fileMap_4790_ = lean_ctor_get(v___y_4774_, 1);
v_options_4791_ = lean_ctor_get(v___y_4774_, 2);
v_currRecDepth_4792_ = lean_ctor_get(v___y_4774_, 3);
v_maxRecDepth_4793_ = lean_ctor_get(v___y_4774_, 4);
v_ref_4794_ = lean_ctor_get(v___y_4774_, 5);
v_currNamespace_4795_ = lean_ctor_get(v___y_4774_, 6);
v_openDecls_4796_ = lean_ctor_get(v___y_4774_, 7);
v_initHeartbeats_4797_ = lean_ctor_get(v___y_4774_, 8);
v_maxHeartbeats_4798_ = lean_ctor_get(v___y_4774_, 9);
v_quotContext_4799_ = lean_ctor_get(v___y_4774_, 10);
v_currMacroScope_4800_ = lean_ctor_get(v___y_4774_, 11);
v_diag_4801_ = lean_ctor_get_uint8(v___y_4774_, sizeof(void*)*14);
v_cancelTk_x3f_4802_ = lean_ctor_get(v___y_4774_, 12);
v_suppressElabErrors_4803_ = lean_ctor_get_uint8(v___y_4774_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4804_ = lean_ctor_get(v___y_4774_, 13);
v___x_4805_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
lean_inc(v_declName_4788_);
v___x_4806_ = l_Lean_MessageData_ofName(v_declName_4788_);
v___x_4807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4805_);
lean_ctor_set(v___x_4807_, 1, v___x_4806_);
v___x_4808_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_4809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4807_);
lean_ctor_set(v___x_4809_, 1, v___x_4808_);
v_ref_4810_ = l_Lean_replaceRef(v_ref_4787_, v_ref_4794_);
lean_inc_ref(v_inheritedTraceOptions_4804_);
lean_inc(v_cancelTk_x3f_4802_);
lean_inc(v_currMacroScope_4800_);
lean_inc(v_quotContext_4799_);
lean_inc(v_maxHeartbeats_4798_);
lean_inc(v_initHeartbeats_4797_);
lean_inc(v_openDecls_4796_);
lean_inc(v_currNamespace_4795_);
lean_inc(v_maxRecDepth_4793_);
lean_inc(v_currRecDepth_4792_);
lean_inc_ref(v_options_4791_);
lean_inc_ref(v_fileMap_4790_);
lean_inc_ref(v_fileName_4789_);
v___x_4811_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4811_, 0, v_fileName_4789_);
lean_ctor_set(v___x_4811_, 1, v_fileMap_4790_);
lean_ctor_set(v___x_4811_, 2, v_options_4791_);
lean_ctor_set(v___x_4811_, 3, v_currRecDepth_4792_);
lean_ctor_set(v___x_4811_, 4, v_maxRecDepth_4793_);
lean_ctor_set(v___x_4811_, 5, v_ref_4810_);
lean_ctor_set(v___x_4811_, 6, v_currNamespace_4795_);
lean_ctor_set(v___x_4811_, 7, v_openDecls_4796_);
lean_ctor_set(v___x_4811_, 8, v_initHeartbeats_4797_);
lean_ctor_set(v___x_4811_, 9, v_maxHeartbeats_4798_);
lean_ctor_set(v___x_4811_, 10, v_quotContext_4799_);
lean_ctor_set(v___x_4811_, 11, v_currMacroScope_4800_);
lean_ctor_set(v___x_4811_, 12, v_cancelTk_x3f_4802_);
lean_ctor_set(v___x_4811_, 13, v_inheritedTraceOptions_4804_);
lean_ctor_set_uint8(v___x_4811_, sizeof(void*)*14, v_diag_4801_);
lean_ctor_set_uint8(v___x_4811_, sizeof(void*)*14 + 1, v_suppressElabErrors_4803_);
v___x_4812_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_4809_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___x_4811_, v___y_4775_);
lean_dec_ref_known(v___x_4811_, 14);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_dec_ref_known(v___x_4812_, 1);
v_a_4778_ = v___x_4784_;
goto v___jp_4777_;
}
else
{
return v___x_4812_;
}
}
}
v___jp_4777_:
{
size_t v___x_4779_; size_t v___x_4780_; 
v___x_4779_ = ((size_t)1ULL);
v___x_4780_ = lean_usize_add(v_i_4768_, v___x_4779_);
v_i_4768_ = v___x_4780_;
v_b_4769_ = v_a_4778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___boxed(lean_object* v___x_4813_, lean_object* v_as_4814_, lean_object* v_sz_4815_, lean_object* v_i_4816_, lean_object* v_b_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
size_t v_sz_boxed_4825_; size_t v_i_boxed_4826_; lean_object* v_res_4827_; 
v_sz_boxed_4825_ = lean_unbox_usize(v_sz_4815_);
lean_dec(v_sz_4815_);
v_i_boxed_4826_ = lean_unbox_usize(v_i_4816_);
lean_dec(v_i_4816_);
v_res_4827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(v___x_4813_, v_as_4814_, v_sz_boxed_4825_, v_i_boxed_4826_, v_b_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
lean_dec(v___y_4821_);
lean_dec_ref(v___y_4820_);
lean_dec(v___y_4819_);
lean_dec_ref(v___y_4818_);
lean_dec_ref(v_as_4814_);
lean_dec(v___x_4813_);
return v_res_4827_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(lean_object* v_values_4828_, lean_object* v_fvars_4829_, lean_object* v___x_4830_, lean_object* v___x_4831_, lean_object* v_as_4832_, lean_object* v_i_4833_, lean_object* v_j_4834_, lean_object* v_bs_4835_){
_start:
{
lean_object* v_zero_4837_; uint8_t v_isZero_4838_; 
v_zero_4837_ = lean_unsigned_to_nat(0u);
v_isZero_4838_ = lean_nat_dec_eq(v_i_4833_, v_zero_4837_);
if (v_isZero_4838_ == 1)
{
lean_object* v___x_4839_; 
lean_dec(v_j_4834_);
lean_dec(v_i_4833_);
lean_dec_ref(v___x_4831_);
lean_dec_ref(v___x_4830_);
v___x_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4839_, 0, v_bs_4835_);
return v___x_4839_;
}
else
{
lean_object* v___x_4840_; lean_object* v_ref_4841_; lean_object* v_attrs_4842_; lean_object* v_shortDeclName_4843_; lean_object* v_declName_4844_; lean_object* v_parentName_x3f_4845_; lean_object* v_binderIds_4846_; lean_object* v_binders_4847_; lean_object* v_type_4848_; lean_object* v_mvar_4849_; lean_object* v_termination_4850_; lean_object* v_docString_x3f_4851_; lean_object* v___x_4852_; lean_object* v_one_4853_; lean_object* v_n_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4840_ = lean_array_fget_borrowed(v_as_4832_, v_j_4834_);
v_ref_4841_ = lean_ctor_get(v___x_4840_, 0);
v_attrs_4842_ = lean_ctor_get(v___x_4840_, 1);
v_shortDeclName_4843_ = lean_ctor_get(v___x_4840_, 2);
v_declName_4844_ = lean_ctor_get(v___x_4840_, 3);
v_parentName_x3f_4845_ = lean_ctor_get(v___x_4840_, 4);
v_binderIds_4846_ = lean_ctor_get(v___x_4840_, 5);
v_binders_4847_ = lean_ctor_get(v___x_4840_, 6);
v_type_4848_ = lean_ctor_get(v___x_4840_, 7);
v_mvar_4849_ = lean_ctor_get(v___x_4840_, 8);
v_termination_4850_ = lean_ctor_get(v___x_4840_, 10);
v_docString_x3f_4851_ = lean_ctor_get(v___x_4840_, 11);
v___x_4852_ = l_Lean_instInhabitedExpr;
v_one_4853_ = lean_unsigned_to_nat(1u);
v_n_4854_ = lean_nat_sub(v_i_4833_, v_one_4853_);
lean_dec(v_i_4833_);
v___x_4855_ = lean_array_get_borrowed(v___x_4852_, v_values_4828_, v_j_4834_);
v___x_4856_ = lean_array_get_size(v_binderIds_4846_);
lean_inc_ref(v_termination_4850_);
v___x_4857_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v___x_4856_, v_termination_4850_, v___x_4855_);
v___x_4858_ = lean_array_get_borrowed(v___x_4852_, v_fvars_4829_, v_j_4834_);
v___x_4859_ = l_Lean_Expr_fvarId_x21(v___x_4858_);
v___x_4860_ = l_Lean_Expr_mvarId_x21(v_mvar_4849_);
lean_inc(v_docString_x3f_4851_);
lean_inc(v_binders_4847_);
lean_inc(v___x_4855_);
lean_inc_ref(v_type_4848_);
lean_inc_ref(v___x_4831_);
lean_inc_ref(v___x_4830_);
lean_inc(v_parentName_x3f_4845_);
lean_inc(v_declName_4844_);
lean_inc(v_shortDeclName_4843_);
lean_inc_ref(v_attrs_4842_);
lean_inc(v_ref_4841_);
v___x_4861_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v___x_4861_, 0, v_ref_4841_);
lean_ctor_set(v___x_4861_, 1, v___x_4859_);
lean_ctor_set(v___x_4861_, 2, v_attrs_4842_);
lean_ctor_set(v___x_4861_, 3, v_shortDeclName_4843_);
lean_ctor_set(v___x_4861_, 4, v_declName_4844_);
lean_ctor_set(v___x_4861_, 5, v_parentName_x3f_4845_);
lean_ctor_set(v___x_4861_, 6, v___x_4830_);
lean_ctor_set(v___x_4861_, 7, v___x_4831_);
lean_ctor_set(v___x_4861_, 8, v_type_4848_);
lean_ctor_set(v___x_4861_, 9, v___x_4855_);
lean_ctor_set(v___x_4861_, 10, v___x_4860_);
lean_ctor_set(v___x_4861_, 11, v___x_4857_);
lean_ctor_set(v___x_4861_, 12, v_binders_4847_);
lean_ctor_set(v___x_4861_, 13, v_docString_x3f_4851_);
v___x_4862_ = lean_nat_add(v_j_4834_, v_one_4853_);
lean_dec(v_j_4834_);
v___x_4863_ = lean_array_push(v_bs_4835_, v___x_4861_);
v_i_4833_ = v_n_4854_;
v_j_4834_ = v___x_4862_;
v_bs_4835_ = v___x_4863_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg___boxed(lean_object* v_values_4865_, lean_object* v_fvars_4866_, lean_object* v___x_4867_, lean_object* v___x_4868_, lean_object* v_as_4869_, lean_object* v_i_4870_, lean_object* v_j_4871_, lean_object* v_bs_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(v_values_4865_, v_fvars_4866_, v___x_4867_, v___x_4868_, v_as_4869_, v_i_4870_, v_j_4871_, v_bs_4872_);
lean_dec_ref(v_as_4869_);
lean_dec_ref(v_fvars_4866_);
lean_dec_ref(v_values_4865_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(lean_object* v_views_4875_, lean_object* v_fvars_4876_, lean_object* v_values_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_){
_start:
{
lean_object* v___x_4885_; lean_object* v_letRecsToLift_4886_; lean_object* v___x_4887_; size_t v_sz_4888_; size_t v___x_4889_; lean_object* v___x_4890_; 
v___x_4885_ = lean_st_ref_get(v_a_4879_);
v_letRecsToLift_4886_ = lean_ctor_get(v___x_4885_, 6);
lean_inc(v_letRecsToLift_4886_);
lean_dec(v___x_4885_);
v___x_4887_ = lean_box(0);
v_sz_4888_ = lean_array_size(v_views_4875_);
v___x_4889_ = ((size_t)0ULL);
v___x_4890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(v_letRecsToLift_4886_, v_views_4875_, v_sz_4888_, v___x_4889_, v___x_4887_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_);
lean_dec(v_letRecsToLift_4886_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_lctx_4891_; lean_object* v_localInstances_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4922_; 
lean_dec_ref_known(v___x_4890_, 1);
v_lctx_4891_ = lean_ctor_get(v_a_4880_, 2);
v_localInstances_4892_ = lean_ctor_get(v_a_4880_, 3);
v___x_4893_ = lean_array_get_size(v_views_4875_);
v___x_4894_ = lean_unsigned_to_nat(0u);
v___x_4895_ = lean_mk_empty_array_with_capacity(v___x_4893_);
lean_inc_ref(v_localInstances_4892_);
lean_inc_ref(v_lctx_4891_);
v___x_4896_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(v_values_4877_, v_fvars_4876_, v_lctx_4891_, v_localInstances_4892_, v_views_4875_, v___x_4893_, v___x_4894_, v___x_4895_);
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4922_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4922_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4901_; lean_object* v_levelNames_4902_; lean_object* v_syntheticMVars_4903_; lean_object* v_pendingMVars_4904_; lean_object* v_mvarErrorInfos_4905_; lean_object* v_levelMVarErrorInfos_4906_; lean_object* v_mvarArgNames_4907_; lean_object* v_letRecsToLift_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4921_; 
v___x_4901_ = lean_st_ref_take(v_a_4879_);
v_levelNames_4902_ = lean_ctor_get(v___x_4901_, 0);
v_syntheticMVars_4903_ = lean_ctor_get(v___x_4901_, 1);
v_pendingMVars_4904_ = lean_ctor_get(v___x_4901_, 2);
v_mvarErrorInfos_4905_ = lean_ctor_get(v___x_4901_, 3);
v_levelMVarErrorInfos_4906_ = lean_ctor_get(v___x_4901_, 4);
v_mvarArgNames_4907_ = lean_ctor_get(v___x_4901_, 5);
v_letRecsToLift_4908_ = lean_ctor_get(v___x_4901_, 6);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4901_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4910_ = v___x_4901_;
v_isShared_4911_ = v_isSharedCheck_4921_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_letRecsToLift_4908_);
lean_inc(v_mvarArgNames_4907_);
lean_inc(v_levelMVarErrorInfos_4906_);
lean_inc(v_mvarErrorInfos_4905_);
lean_inc(v_pendingMVars_4904_);
lean_inc(v_syntheticMVars_4903_);
lean_inc(v_levelNames_4902_);
lean_dec(v___x_4901_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4921_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4915_; 
v___x_4912_ = lean_array_to_list(v_a_4897_);
v___x_4913_ = l_List_appendTR___redArg(v___x_4912_, v_letRecsToLift_4908_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 6, v___x_4913_);
v___x_4915_ = v___x_4910_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_levelNames_4902_);
lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_syntheticMVars_4903_);
lean_ctor_set(v_reuseFailAlloc_4920_, 2, v_pendingMVars_4904_);
lean_ctor_set(v_reuseFailAlloc_4920_, 3, v_mvarErrorInfos_4905_);
lean_ctor_set(v_reuseFailAlloc_4920_, 4, v_levelMVarErrorInfos_4906_);
lean_ctor_set(v_reuseFailAlloc_4920_, 5, v_mvarArgNames_4907_);
lean_ctor_set(v_reuseFailAlloc_4920_, 6, v___x_4913_);
v___x_4915_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
lean_object* v___x_4916_; lean_object* v___x_4918_; 
v___x_4916_ = lean_st_ref_set(v_a_4879_, v___x_4915_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4887_);
v___x_4918_ = v___x_4899_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4887_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
}
}
else
{
return v___x_4890_;
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
lean_dec_ref(v_a_4928_);
lean_dec(v_a_4927_);
lean_dec_ref(v_a_4926_);
lean_dec_ref(v_values_4925_);
lean_dec_ref(v_fvars_4924_);
lean_dec_ref(v_views_4923_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2(lean_object* v_values_4934_, lean_object* v_fvars_4935_, lean_object* v___x_4936_, lean_object* v___x_4937_, lean_object* v_as_4938_, lean_object* v_i_4939_, lean_object* v_j_4940_, lean_object* v_inv_4941_, lean_object* v_bs_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
lean_object* v___x_4950_; 
v___x_4950_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(v_values_4934_, v_fvars_4935_, v___x_4936_, v___x_4937_, v_as_4938_, v_i_4939_, v_j_4940_, v_bs_4942_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___boxed(lean_object* v_values_4951_, lean_object* v_fvars_4952_, lean_object* v___x_4953_, lean_object* v___x_4954_, lean_object* v_as_4955_, lean_object* v_i_4956_, lean_object* v_j_4957_, lean_object* v_inv_4958_, lean_object* v_bs_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2(v_values_4951_, v_fvars_4952_, v___x_4953_, v___x_4954_, v_as_4955_, v_i_4956_, v_j_4957_, v_inv_4958_, v_bs_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
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
lean_inc(v___x_5009_);
lean_inc(v_ref_5008_);
v___x_5010_ = l_Lean_Elab_Term_addLocalVarInfo(v_ref_5008_, v___x_5009_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5014_; 
lean_dec_ref_known(v___x_5010_, 1);
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
lean_dec(v___y_5040_);
lean_dec_ref(v___y_5039_);
lean_dec(v___y_5038_);
lean_dec_ref(v___y_5037_);
lean_dec(v___y_5036_);
lean_dec_ref(v___y_5035_);
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
v___x_5062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(v_decls_5045_, v_sz_5060_, v___x_5061_, v___x_5059_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v___x_5063_; 
lean_dec_ref_known(v___x_5062_, 1);
v___x_5063_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(v_a_5046_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v_a_5064_; uint8_t v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5063_, 1);
v___x_5065_ = 1;
v___x_5066_ = lean_box(0);
v___x_5067_ = l_Lean_Elab_Term_elabTermEnsuringType(v_body_5047_, v_expectedType_x3f_5048_, v___x_5065_, v___x_5065_, v___x_5066_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v_a_5068_; lean_object* v___x_5069_; 
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_a_5068_);
lean_dec_ref_known(v___x_5067_, 1);
v___x_5069_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(v_decls_5045_, v_fvars_5049_, v_a_5064_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec(v_a_5064_);
if (lean_obj_tag(v___x_5069_) == 0)
{
uint8_t v___x_5070_; uint8_t v___x_5071_; lean_object* v___x_5072_; 
lean_dec_ref_known(v___x_5069_, 1);
v___x_5070_ = 0;
v___x_5071_ = 1;
v___x_5072_ = l_Lean_Meta_mkLambdaFVars(v_fvars_5049_, v_a_5068_, v___x_5070_, v___x_5065_, v___x_5070_, v___x_5065_, v___x_5071_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
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
lean_dec_ref(v_fvars_5049_);
lean_dec_ref(v_decls_5045_);
return v___x_5067_;
}
}
else
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5098_; 
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
lean_dec(v___y_5117_);
lean_dec_ref(v___y_5116_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec(lean_object* v_stx_5120_, lean_object* v_expectedType_x3f_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v___x_5129_; 
v___x_5129_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(v_stx_5120_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v_decls_5131_; lean_object* v_body_5132_; lean_object* v___f_5133_; lean_object* v___x_5134_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
v_decls_5131_ = lean_ctor_get(v_a_5130_, 0);
lean_inc_ref_n(v_decls_5131_, 2);
v_body_5132_ = lean_ctor_get(v_a_5130_, 1);
lean_inc(v_body_5132_);
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
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
lean_dec(v_a_5148_);
lean_dec_ref(v_a_5147_);
lean_dec(v_a_5146_);
lean_dec_ref(v_a_5145_);
lean_dec(v_stx_5143_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1(){
_start:
{
lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v___x_5166_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5167_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1));
v___x_5168_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3));
v___x_5169_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetRec___boxed), 9, 0);
v___x_5170_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5166_, v___x_5167_, v___x_5168_, v___x_5169_);
return v___x_5170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___boxed(lean_object* v_a_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1();
return v_res_5172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3(){
_start:
{
lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v___x_5199_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3));
v___x_5200_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6));
v___x_5201_ = l_Lean_addBuiltinDeclarationRanges(v___x_5199_, v___x_5200_);
return v___x_5201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___boxed(lean_object* v_a_5202_){
_start:
{
lean_object* v_res_5203_; 
v_res_5203_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3();
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
res = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3();
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
