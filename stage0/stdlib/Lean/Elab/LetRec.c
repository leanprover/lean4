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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1;
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
lean_dec_ref(v___x_191_);
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
lean_object* v___x_240_; lean_object* v_env_241_; lean_object* v_nextMacroScope_242_; lean_object* v_ngen_243_; lean_object* v_auxDeclNGen_244_; lean_object* v_traceState_245_; lean_object* v_messages_246_; lean_object* v_infoState_247_; lean_object* v_snapshotTasks_248_; lean_object* v_newDecls_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_277_; 
v___x_240_ = lean_st_ref_take(v___y_237_);
v_env_241_ = lean_ctor_get(v___x_240_, 0);
v_nextMacroScope_242_ = lean_ctor_get(v___x_240_, 1);
v_ngen_243_ = lean_ctor_get(v___x_240_, 2);
v_auxDeclNGen_244_ = lean_ctor_get(v___x_240_, 3);
v_traceState_245_ = lean_ctor_get(v___x_240_, 4);
v_messages_246_ = lean_ctor_get(v___x_240_, 6);
v_infoState_247_ = lean_ctor_get(v___x_240_, 7);
v_snapshotTasks_248_ = lean_ctor_get(v___x_240_, 8);
v_newDecls_249_ = lean_ctor_get(v___x_240_, 9);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v___x_240_, 5);
lean_dec(v_unused_278_);
v___x_251_ = v___x_240_;
v_isShared_252_ = v_isSharedCheck_277_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_newDecls_249_);
lean_inc(v_snapshotTasks_248_);
lean_inc(v_infoState_247_);
lean_inc(v_messages_246_);
lean_inc(v_traceState_245_);
lean_inc(v_auxDeclNGen_244_);
lean_inc(v_ngen_243_);
lean_inc(v_nextMacroScope_242_);
lean_inc(v_env_241_);
lean_dec(v___x_240_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_277_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_253_ = l_Lean_declRangeExt;
v___x_254_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_253_, v_env_241_, v_declName_234_, v_declRanges_235_);
v___x_255_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 5, v___x_255_);
lean_ctor_set(v___x_251_, 0, v___x_254_);
v___x_257_ = v___x_251_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_nextMacroScope_242_);
lean_ctor_set(v_reuseFailAlloc_276_, 2, v_ngen_243_);
lean_ctor_set(v_reuseFailAlloc_276_, 3, v_auxDeclNGen_244_);
lean_ctor_set(v_reuseFailAlloc_276_, 4, v_traceState_245_);
lean_ctor_set(v_reuseFailAlloc_276_, 5, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_276_, 6, v_messages_246_);
lean_ctor_set(v_reuseFailAlloc_276_, 7, v_infoState_247_);
lean_ctor_set(v_reuseFailAlloc_276_, 8, v_snapshotTasks_248_);
lean_ctor_set(v_reuseFailAlloc_276_, 9, v_newDecls_249_);
v___x_257_ = v_reuseFailAlloc_276_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_mctx_260_; lean_object* v_zetaDeltaFVarIds_261_; lean_object* v_postponed_262_; lean_object* v_diag_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_274_; 
v___x_258_ = lean_st_ref_set(v___y_237_, v___x_257_);
v___x_259_ = lean_st_ref_take(v___y_236_);
v_mctx_260_ = lean_ctor_get(v___x_259_, 0);
v_zetaDeltaFVarIds_261_ = lean_ctor_get(v___x_259_, 2);
v_postponed_262_ = lean_ctor_get(v___x_259_, 3);
v_diag_263_ = lean_ctor_get(v___x_259_, 4);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v___x_259_, 1);
lean_dec(v_unused_275_);
v___x_265_ = v___x_259_;
v_isShared_266_ = v_isSharedCheck_274_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_diag_263_);
lean_inc(v_postponed_262_);
lean_inc(v_zetaDeltaFVarIds_261_);
lean_inc(v_mctx_260_);
lean_dec(v___x_259_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_274_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 1, v___x_267_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_mctx_260_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_zetaDeltaFVarIds_261_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_postponed_262_);
lean_ctor_set(v_reuseFailAlloc_273_, 4, v_diag_263_);
v___x_269_ = v_reuseFailAlloc_273_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_st_ref_set(v___y_236_, v___x_269_);
v___x_271_ = lean_box(0);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref(v_declRanges_235_);
lean_dec(v_declName_234_);
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___boxed(lean_object* v_declName_281_, lean_object* v_declRanges_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_281_, v_declRanges_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(lean_object* v_declName_287_, lean_object* v_rangeStx_288_, lean_object* v_selectionRangeStx_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_314_; 
v___x_297_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_rangeStx_288_, v___y_294_);
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_314_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_314_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_314_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
if (lean_obj_tag(v_a_298_) == 1)
{
lean_object* v_val_302_; lean_object* v___x_303_; lean_object* v_a_304_; lean_object* v_a_306_; 
lean_del_object(v___x_300_);
v_val_302_ = lean_ctor_get(v_a_298_, 0);
lean_inc(v_val_302_);
lean_dec_ref(v_a_298_);
v___x_303_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_selectionRangeStx_289_, v___y_294_);
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v___x_303_);
if (lean_obj_tag(v_a_304_) == 0)
{
lean_inc(v_val_302_);
v_a_306_ = v_val_302_;
goto v___jp_305_;
}
else
{
lean_object* v_val_309_; 
v_val_309_ = lean_ctor_get(v_a_304_, 0);
lean_inc(v_val_309_);
lean_dec_ref(v_a_304_);
v_a_306_ = v_val_309_;
goto v___jp_305_;
}
v___jp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_val_302_);
lean_ctor_set(v___x_307_, 1, v_a_306_);
v___x_308_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_287_, v___x_307_, v___y_293_, v___y_295_);
return v___x_308_;
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec(v_a_298_);
lean_dec(v_declName_287_);
v___x_310_ = lean_box(0);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_310_);
v___x_312_ = v___x_300_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2___boxed(lean_object* v_declName_315_, lean_object* v_rangeStx_316_, lean_object* v_selectionRangeStx_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(v_declName_315_, v_rangeStx_316_, v_selectionRangeStx_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v_selectionRangeStx_317_);
lean_dec(v_rangeStx_316_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0(lean_object* v___x_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_326_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0___boxed(lean_object* v___x_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0(v___x_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7(lean_object* v_00_u03b1_344_, lean_object* v_ref_345_, lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_ref_345_, v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___boxed(lean_object* v_00_u03b1_355_, lean_object* v_ref_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7(v_00_u03b1_355_, v_ref_356_, v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v_ref_356_);
return v_res_365_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__9));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__18));
v___x_408_ = l_Lean_stringToMessageData(v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__20));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(lean_object* v_stx_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
if (lean_obj_tag(v_stx_424_) == 0)
{
lean_object* v___x_432_; lean_object* v_terminationBy_x3f_x3f_433_; lean_object* v_terminationBy_x3f_434_; lean_object* v_partialFixpoint_x3f_435_; lean_object* v_decreasingBy_x3f_436_; lean_object* v_extraParams_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_432_ = l_Lean_Elab_TerminationHints_none;
v_terminationBy_x3f_x3f_433_ = lean_ctor_get(v___x_432_, 1);
v_terminationBy_x3f_434_ = lean_ctor_get(v___x_432_, 2);
v_partialFixpoint_x3f_435_ = lean_ctor_get(v___x_432_, 3);
v_decreasingBy_x3f_436_ = lean_ctor_get(v___x_432_, 4);
v_extraParams_437_ = lean_ctor_get(v___x_432_, 5);
lean_inc(v_extraParams_437_);
lean_inc(v_decreasingBy_x3f_436_);
lean_inc(v_partialFixpoint_x3f_435_);
lean_inc(v_terminationBy_x3f_434_);
lean_inc(v_terminationBy_x3f_x3f_433_);
v___x_438_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_438_, 0, v_stx_424_);
lean_ctor_set(v___x_438_, 1, v_terminationBy_x3f_x3f_433_);
lean_ctor_set(v___x_438_, 2, v_terminationBy_x3f_434_);
lean_ctor_set(v___x_438_, 3, v_partialFixpoint_x3f_435_);
lean_ctor_set(v___x_438_, 4, v_decreasingBy_x3f_436_);
lean_ctor_set(v___x_438_, 5, v_extraParams_437_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
else
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__4));
lean_inc(v_stx_424_);
v___x_441_ = l_Lean_Syntax_isOfKind(v_stx_424_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_442_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_443_ = lean_box(0);
lean_inc_n(v_stx_424_, 2);
v___x_444_ = l_Lean_Syntax_formatStx(v_stx_424_, v___x_443_, v___x_441_);
v___x_445_ = l_Std_Format_defWidth;
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = l_Std_Format_pretty(v___x_444_, v___x_445_, v___x_446_, v___x_446_);
v___x_448_ = lean_string_append(v___x_442_, v___x_447_);
lean_dec_ref(v___x_447_);
v___x_449_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_450_ = lean_string_append(v___x_448_, v___x_449_);
v___x_451_ = l_Lean_Syntax_getKind(v_stx_424_);
v___x_452_ = 1;
v___x_453_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_451_, v___x_452_);
v___x_454_ = lean_string_append(v___x_450_, v___x_453_);
lean_dec_ref(v___x_453_);
v___x_455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
v___x_456_ = l_Lean_MessageData_ofFormat(v___x_455_);
v___x_457_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_424_, v___x_456_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v_stx_424_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v_partialFixpoint_x3f_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v_term_x3f_524_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v_term_x3f_540_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v_term_x3f_556_; lean_object* v___y_561_; lean_object* v_val_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v_terminationBy_x3f_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v_terminationBy_x3f_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; uint8_t v___y_630_; uint8_t v___y_631_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_672_; uint8_t v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v_s_701_; lean_object* v___y_734_; lean_object* v_val_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v_terminationBy_x3f_x3f_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v_d_x3f_827_; lean_object* v_t_x3f_836_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_458_ = lean_unsigned_to_nat(0u);
v___x_874_ = l_Lean_Syntax_getArg(v_stx_424_, v___x_458_);
v___x_875_ = l_Lean_Syntax_isNone(v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_874_);
v___x_877_ = l_Lean_Syntax_matchesNull(v___x_874_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v___x_874_);
v___x_878_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_879_ = lean_box(0);
lean_inc_n(v_stx_424_, 2);
v___x_880_ = l_Lean_Syntax_formatStx(v_stx_424_, v___x_879_, v___x_877_);
v___x_881_ = l_Std_Format_defWidth;
v___x_882_ = l_Std_Format_pretty(v___x_880_, v___x_881_, v___x_458_, v___x_458_);
v___x_883_ = lean_string_append(v___x_878_, v___x_882_);
lean_dec_ref(v___x_882_);
v___x_884_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_885_ = lean_string_append(v___x_883_, v___x_884_);
v___x_886_ = l_Lean_Syntax_getKind(v_stx_424_);
v___x_887_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_886_, v___x_441_);
v___x_888_ = lean_string_append(v___x_885_, v___x_887_);
lean_dec_ref(v___x_887_);
v___x_889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
v___x_890_ = l_Lean_MessageData_ofFormat(v___x_889_);
v___x_891_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_424_, v___x_890_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v_stx_424_);
return v___x_891_;
}
else
{
lean_object* v_t_x3f_892_; lean_object* v___x_893_; 
v_t_x3f_892_ = l_Lean_Syntax_getArg(v___x_874_, v___x_458_);
lean_dec(v___x_874_);
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v_t_x3f_892_);
v_t_x3f_836_ = v___x_893_;
goto v___jp_835_;
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v___x_874_);
v___x_894_ = lean_box(0);
v_t_x3f_836_ = v___x_894_;
goto v___jp_835_;
}
v___jp_459_:
{
lean_object* v___x_470_; 
lean_inc(v___y_463_);
lean_inc_ref(v___y_461_);
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_462_);
lean_inc_ref(v___y_468_);
v___x_470_ = lean_apply_7(v___y_469_, v___y_468_, v___y_462_, v___y_466_, v___y_467_, v___y_461_, v___y_463_, lean_box(0));
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_480_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_480_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_480_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_480_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v_a_471_);
v___x_476_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_476_, 0, v_stx_424_);
lean_ctor_set(v___x_476_, 1, v___y_460_);
lean_ctor_set(v___x_476_, 2, v___y_464_);
lean_ctor_set(v___x_476_, 3, v___y_465_);
lean_ctor_set(v___x_476_, 4, v___x_475_);
lean_ctor_set(v___x_476_, 5, v___x_458_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_476_);
v___x_478_ = v___x_473_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v___y_465_);
lean_dec(v___y_464_);
lean_dec(v___y_460_);
lean_dec(v_stx_424_);
v_a_481_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_470_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_470_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
v___jp_489_:
{
if (lean_obj_tag(v___y_493_) == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_502_, 0, v_stx_424_);
lean_ctor_set(v___x_502_, 1, v___y_490_);
lean_ctor_set(v___x_502_, 2, v___y_492_);
lean_ctor_set(v___x_502_, 3, v_partialFixpoint_x3f_494_);
lean_ctor_set(v___x_502_, 4, v___x_501_);
lean_ctor_set(v___x_502_, 5, v___x_458_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
else
{
lean_object* v_val_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_val_504_ = lean_ctor_get(v___y_493_, 0);
lean_inc_n(v_val_504_, 2);
lean_dec_ref(v___y_493_);
v___x_505_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8));
v___x_506_ = l_Lean_Syntax_isOfKind(v_val_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__10);
v___x_508_ = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___boxed), 10, 3);
lean_closure_set(v___x_508_, 0, lean_box(0));
lean_closure_set(v___x_508_, 1, v_val_504_);
lean_closure_set(v___x_508_, 2, v___x_507_);
v___y_460_ = v___y_490_;
v___y_461_ = v___y_499_;
v___y_462_ = v___y_496_;
v___y_463_ = v___y_500_;
v___y_464_ = v___y_492_;
v___y_465_ = v_partialFixpoint_x3f_494_;
v___y_466_ = v___y_497_;
v___y_467_ = v___y_498_;
v___y_468_ = v___y_495_;
v___y_469_ = v___x_508_;
goto v___jp_459_;
}
else
{
lean_object* v_tactic_509_; lean_object* v___x_510_; lean_object* v___f_511_; 
v_tactic_509_ = l_Lean_Syntax_getArg(v_val_504_, v___y_491_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_val_504_);
lean_ctor_set(v___x_510_, 1, v_tactic_509_);
v___f_511_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_511_, 0, v___x_510_);
v___y_460_ = v___y_490_;
v___y_461_ = v___y_499_;
v___y_462_ = v___y_496_;
v___y_463_ = v___y_500_;
v___y_464_ = v___y_492_;
v___y_465_ = v_partialFixpoint_x3f_494_;
v___y_466_ = v___y_497_;
v___y_467_ = v___y_498_;
v___y_468_ = v___y_495_;
v___y_469_ = v___f_511_;
goto v___jp_459_;
}
}
}
v___jp_512_:
{
uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = 0;
v___x_526_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_526_, 0, v___y_520_);
lean_ctor_set(v___x_526_, 1, v_term_x3f_524_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*2, v___x_525_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___y_490_ = v___y_513_;
v___y_491_ = v___y_514_;
v___y_492_ = v___y_517_;
v___y_493_ = v___y_521_;
v_partialFixpoint_x3f_494_ = v___x_527_;
v___y_495_ = v___y_519_;
v___y_496_ = v___y_518_;
v___y_497_ = v___y_516_;
v___y_498_ = v___y_523_;
v___y_499_ = v___y_522_;
v___y_500_ = v___y_515_;
goto v___jp_489_;
}
v___jp_528_:
{
uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = 1;
v___x_542_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_542_, 0, v___y_536_);
lean_ctor_set(v___x_542_, 1, v_term_x3f_540_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*2, v___x_541_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
v___y_490_ = v___y_529_;
v___y_491_ = v___y_530_;
v___y_492_ = v___y_533_;
v___y_493_ = v___y_537_;
v_partialFixpoint_x3f_494_ = v___x_543_;
v___y_495_ = v___y_535_;
v___y_496_ = v___y_534_;
v___y_497_ = v___y_532_;
v___y_498_ = v___y_539_;
v___y_499_ = v___y_538_;
v___y_500_ = v___y_531_;
goto v___jp_489_;
}
v___jp_544_:
{
uint8_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = 2;
v___x_558_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_558_, 0, v___y_552_);
lean_ctor_set(v___x_558_, 1, v_term_x3f_556_);
lean_ctor_set_uint8(v___x_558_, sizeof(void*)*2, v___x_557_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___y_490_ = v___y_545_;
v___y_491_ = v___y_546_;
v___y_492_ = v___y_549_;
v___y_493_ = v___y_553_;
v_partialFixpoint_x3f_494_ = v___x_559_;
v___y_495_ = v___y_551_;
v___y_496_ = v___y_550_;
v___y_497_ = v___y_548_;
v___y_498_ = v___y_555_;
v___y_499_ = v___y_554_;
v___y_500_ = v___y_547_;
goto v___jp_489_;
}
v___jp_560_:
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12));
lean_inc(v_val_562_);
v___x_573_ = l_Lean_Syntax_isOfKind(v_val_562_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14));
lean_inc(v_val_562_);
v___x_575_ = l_Lean_Syntax_isOfKind(v_val_562_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16));
lean_inc(v_val_562_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_val_562_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec(v_val_562_);
v___x_578_ = lean_box(0);
v___y_490_ = v___y_561_;
v___y_491_ = v___y_563_;
v___y_492_ = v_terminationBy_x3f_565_;
v___y_493_ = v___y_564_;
v_partialFixpoint_x3f_494_ = v___x_578_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
v___y_500_ = v___y_571_;
goto v___jp_489_;
}
else
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = l_Lean_Syntax_getArg(v_val_562_, v___y_563_);
v___x_580_ = l_Lean_Syntax_isNone(v___x_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_579_);
v___x_582_ = l_Lean_Syntax_matchesNull(v___x_579_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_dec(v___x_579_);
lean_dec(v_val_562_);
v___x_583_ = lean_box(0);
v___y_490_ = v___y_561_;
v___y_491_ = v___y_563_;
v___y_492_ = v_terminationBy_x3f_565_;
v___y_493_ = v___y_564_;
v_partialFixpoint_x3f_494_ = v___x_583_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
v___y_500_ = v___y_571_;
goto v___jp_489_;
}
else
{
lean_object* v_term_x3f_584_; lean_object* v___x_585_; 
v_term_x3f_584_ = l_Lean_Syntax_getArg(v___x_579_, v___y_563_);
lean_dec(v___x_579_);
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_term_x3f_584_);
v___y_545_ = v___y_561_;
v___y_546_ = v___y_563_;
v___y_547_ = v___y_571_;
v___y_548_ = v___y_568_;
v___y_549_ = v_terminationBy_x3f_565_;
v___y_550_ = v___y_567_;
v___y_551_ = v___y_566_;
v___y_552_ = v_val_562_;
v___y_553_ = v___y_564_;
v___y_554_ = v___y_570_;
v___y_555_ = v___y_569_;
v_term_x3f_556_ = v___x_585_;
goto v___jp_544_;
}
}
else
{
lean_object* v___x_586_; 
lean_dec(v___x_579_);
v___x_586_ = lean_box(0);
v___y_545_ = v___y_561_;
v___y_546_ = v___y_563_;
v___y_547_ = v___y_571_;
v___y_548_ = v___y_568_;
v___y_549_ = v_terminationBy_x3f_565_;
v___y_550_ = v___y_567_;
v___y_551_ = v___y_566_;
v___y_552_ = v_val_562_;
v___y_553_ = v___y_564_;
v___y_554_ = v___y_570_;
v___y_555_ = v___y_569_;
v_term_x3f_556_ = v___x_586_;
goto v___jp_544_;
}
}
}
else
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = l_Lean_Syntax_getArg(v_val_562_, v___y_563_);
v___x_588_ = l_Lean_Syntax_isNone(v___x_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_587_);
v___x_590_ = l_Lean_Syntax_matchesNull(v___x_587_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec(v___x_587_);
lean_dec(v_val_562_);
v___x_591_ = lean_box(0);
v___y_490_ = v___y_561_;
v___y_491_ = v___y_563_;
v___y_492_ = v_terminationBy_x3f_565_;
v___y_493_ = v___y_564_;
v_partialFixpoint_x3f_494_ = v___x_591_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
v___y_500_ = v___y_571_;
goto v___jp_489_;
}
else
{
lean_object* v_term_x3f_592_; lean_object* v___x_593_; 
v_term_x3f_592_ = l_Lean_Syntax_getArg(v___x_587_, v___y_563_);
lean_dec(v___x_587_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v_term_x3f_592_);
v___y_529_ = v___y_561_;
v___y_530_ = v___y_563_;
v___y_531_ = v___y_571_;
v___y_532_ = v___y_568_;
v___y_533_ = v_terminationBy_x3f_565_;
v___y_534_ = v___y_567_;
v___y_535_ = v___y_566_;
v___y_536_ = v_val_562_;
v___y_537_ = v___y_564_;
v___y_538_ = v___y_570_;
v___y_539_ = v___y_569_;
v_term_x3f_540_ = v___x_593_;
goto v___jp_528_;
}
}
else
{
lean_object* v___x_594_; 
lean_dec(v___x_587_);
v___x_594_ = lean_box(0);
v___y_529_ = v___y_561_;
v___y_530_ = v___y_563_;
v___y_531_ = v___y_571_;
v___y_532_ = v___y_568_;
v___y_533_ = v_terminationBy_x3f_565_;
v___y_534_ = v___y_567_;
v___y_535_ = v___y_566_;
v___y_536_ = v_val_562_;
v___y_537_ = v___y_564_;
v___y_538_ = v___y_570_;
v___y_539_ = v___y_569_;
v_term_x3f_540_ = v___x_594_;
goto v___jp_528_;
}
}
}
else
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = l_Lean_Syntax_getArg(v_val_562_, v___y_563_);
v___x_596_ = l_Lean_Syntax_isNone(v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_595_);
v___x_598_ = l_Lean_Syntax_matchesNull(v___x_595_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
lean_dec(v___x_595_);
lean_dec(v_val_562_);
v___x_599_ = lean_box(0);
v___y_490_ = v___y_561_;
v___y_491_ = v___y_563_;
v___y_492_ = v_terminationBy_x3f_565_;
v___y_493_ = v___y_564_;
v_partialFixpoint_x3f_494_ = v___x_599_;
v___y_495_ = v___y_566_;
v___y_496_ = v___y_567_;
v___y_497_ = v___y_568_;
v___y_498_ = v___y_569_;
v___y_499_ = v___y_570_;
v___y_500_ = v___y_571_;
goto v___jp_489_;
}
else
{
lean_object* v_term_x3f_600_; lean_object* v___x_601_; 
v_term_x3f_600_ = l_Lean_Syntax_getArg(v___x_595_, v___y_563_);
lean_dec(v___x_595_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_term_x3f_600_);
v___y_513_ = v___y_561_;
v___y_514_ = v___y_563_;
v___y_515_ = v___y_571_;
v___y_516_ = v___y_568_;
v___y_517_ = v_terminationBy_x3f_565_;
v___y_518_ = v___y_567_;
v___y_519_ = v___y_566_;
v___y_520_ = v_val_562_;
v___y_521_ = v___y_564_;
v___y_522_ = v___y_570_;
v___y_523_ = v___y_569_;
v_term_x3f_524_ = v___x_601_;
goto v___jp_512_;
}
}
else
{
lean_object* v___x_602_; 
lean_dec(v___x_595_);
v___x_602_ = lean_box(0);
v___y_513_ = v___y_561_;
v___y_514_ = v___y_563_;
v___y_515_ = v___y_571_;
v___y_516_ = v___y_568_;
v___y_517_ = v_terminationBy_x3f_565_;
v___y_518_ = v___y_567_;
v___y_519_ = v___y_566_;
v___y_520_ = v_val_562_;
v___y_521_ = v___y_564_;
v___y_522_ = v___y_570_;
v___y_523_ = v___y_569_;
v_term_x3f_524_ = v___x_602_;
goto v___jp_512_;
}
}
}
v___jp_603_:
{
if (lean_obj_tag(v___y_605_) == 1)
{
lean_object* v_val_615_; 
v_val_615_ = lean_ctor_get(v___y_605_, 0);
lean_inc(v_val_615_);
lean_dec_ref(v___y_605_);
v___y_561_ = v___y_604_;
v_val_562_ = v_val_615_;
v___y_563_ = v___y_606_;
v___y_564_ = v___y_607_;
v_terminationBy_x3f_565_ = v_terminationBy_x3f_608_;
v___y_566_ = v___y_609_;
v___y_567_ = v___y_610_;
v___y_568_ = v___y_611_;
v___y_569_ = v___y_612_;
v___y_570_ = v___y_613_;
v___y_571_ = v___y_614_;
goto v___jp_560_;
}
else
{
lean_object* v___x_616_; 
lean_dec(v___y_605_);
v___x_616_ = lean_box(0);
v___y_490_ = v___y_604_;
v___y_491_ = v___y_606_;
v___y_492_ = v_terminationBy_x3f_608_;
v___y_493_ = v___y_607_;
v_partialFixpoint_x3f_494_ = v___x_616_;
v___y_495_ = v___y_609_;
v___y_496_ = v___y_610_;
v___y_497_ = v___y_611_;
v___y_498_ = v___y_612_;
v___y_499_ = v___y_613_;
v___y_500_ = v___y_614_;
goto v___jp_489_;
}
}
v___jp_617_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__17));
v___x_633_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_633_, 0, v___y_629_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
lean_ctor_set(v___x_633_, 2, v___y_621_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3, v___y_631_);
lean_ctor_set_uint8(v___x_633_, sizeof(void*)*3 + 1, v___y_630_);
v___x_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
v___y_604_ = v___y_618_;
v___y_605_ = v___y_623_;
v___y_606_ = v___y_624_;
v___y_607_ = v___y_628_;
v_terminationBy_x3f_608_ = v___x_634_;
v___y_609_ = v___y_622_;
v___y_610_ = v___y_626_;
v___y_611_ = v___y_619_;
v___y_612_ = v___y_625_;
v___y_613_ = v___y_620_;
v___y_614_ = v___y_627_;
goto v___jp_603_;
}
v___jp_635_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_box(0);
v___y_604_ = v___y_636_;
v___y_605_ = v___y_637_;
v___y_606_ = v___y_638_;
v___y_607_ = v___y_644_;
v_terminationBy_x3f_608_ = v___x_646_;
v___y_609_ = v___y_645_;
v___y_610_ = v___y_643_;
v___y_611_ = v___y_639_;
v___y_612_ = v___y_641_;
v___y_613_ = v___y_640_;
v___y_614_ = v___y_642_;
goto v___jp_603_;
}
v___jp_647_:
{
lean_object* v___x_658_; 
v___x_658_ = lean_box(0);
v___y_604_ = v___y_648_;
v___y_605_ = v___y_649_;
v___y_606_ = v___y_650_;
v___y_607_ = v___y_656_;
v_terminationBy_x3f_608_ = v___x_658_;
v___y_609_ = v___y_657_;
v___y_610_ = v___y_655_;
v___y_611_ = v___y_651_;
v___y_612_ = v___y_653_;
v___y_613_ = v___y_652_;
v___y_614_ = v___y_654_;
goto v___jp_603_;
}
v___jp_659_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_box(0);
v___y_604_ = v___y_660_;
v___y_605_ = v___y_661_;
v___y_606_ = v___y_662_;
v___y_607_ = v___y_668_;
v_terminationBy_x3f_608_ = v___x_670_;
v___y_609_ = v___y_669_;
v___y_610_ = v___y_667_;
v___y_611_ = v___y_663_;
v___y_612_ = v___y_665_;
v___y_613_ = v___y_664_;
v___y_614_ = v___y_666_;
goto v___jp_603_;
}
v___jp_671_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_687_, 0, v___y_685_);
lean_ctor_set(v___x_687_, 1, v___y_676_);
lean_ctor_set(v___x_687_, 2, v___y_680_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*3, v___y_686_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*3 + 1, v___y_673_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
v___y_604_ = v___y_672_;
v___y_605_ = v___y_678_;
v___y_606_ = v___y_679_;
v___y_607_ = v___y_684_;
v_terminationBy_x3f_608_ = v___x_688_;
v___y_609_ = v___y_677_;
v___y_610_ = v___y_682_;
v___y_611_ = v___y_674_;
v___y_612_ = v___y_681_;
v___y_613_ = v___y_675_;
v___y_614_ = v___y_683_;
goto v___jp_603_;
}
v___jp_689_:
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_unsigned_to_nat(2u);
v___x_703_ = l_Lean_Syntax_getArg(v___y_699_, v___x_702_);
lean_inc(v___x_703_);
v___x_704_ = l_Lean_Syntax_matchesNull(v___x_703_, v___x_702_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; 
v___x_705_ = l_Lean_Syntax_matchesNull(v___x_703_, v___x_458_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_s_701_);
lean_dec(v___y_698_);
lean_dec(v___y_691_);
lean_dec(v___y_690_);
lean_dec(v_stx_424_);
v___x_706_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_707_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___y_699_, v___x_706_, v___y_700_, v___y_697_, v___y_693_, v___y_695_, v___y_694_, v___y_696_);
lean_dec(v___y_699_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v___x_716_; lean_object* v_body_717_; 
v___x_716_ = lean_unsigned_to_nat(3u);
v_body_717_ = l_Lean_Syntax_getArg(v___y_699_, v___x_716_);
if (lean_obj_tag(v_s_701_) == 0)
{
v___y_618_ = v___y_690_;
v___y_619_ = v___y_693_;
v___y_620_ = v___y_694_;
v___y_621_ = v_body_717_;
v___y_622_ = v___y_700_;
v___y_623_ = v___y_691_;
v___y_624_ = v___y_692_;
v___y_625_ = v___y_695_;
v___y_626_ = v___y_697_;
v___y_627_ = v___y_696_;
v___y_628_ = v___y_698_;
v___y_629_ = v___y_699_;
v___y_630_ = v___x_704_;
v___y_631_ = v___x_704_;
goto v___jp_617_;
}
else
{
lean_dec_ref(v_s_701_);
v___y_618_ = v___y_690_;
v___y_619_ = v___y_693_;
v___y_620_ = v___y_694_;
v___y_621_ = v_body_717_;
v___y_622_ = v___y_700_;
v___y_623_ = v___y_691_;
v___y_624_ = v___y_692_;
v___y_625_ = v___y_695_;
v___y_626_ = v___y_697_;
v___y_627_ = v___y_696_;
v___y_628_ = v___y_698_;
v___y_629_ = v___y_699_;
v___y_630_ = v___x_704_;
v___y_631_ = v___x_705_;
goto v___jp_617_;
}
}
}
else
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_Syntax_getArg(v___x_703_, v___x_458_);
lean_dec(v___x_703_);
lean_inc(v___x_718_);
v___x_719_ = l_Lean_Syntax_matchesNull(v___x_718_, v___x_458_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v_body_721_; lean_object* v_vars_722_; 
v___x_720_ = lean_unsigned_to_nat(3u);
v_body_721_ = l_Lean_Syntax_getArg(v___y_699_, v___x_720_);
v_vars_722_ = l_Lean_Syntax_getArgs(v___x_718_);
lean_dec(v___x_718_);
if (lean_obj_tag(v_s_701_) == 0)
{
v___y_672_ = v___y_690_;
v___y_673_ = v___x_719_;
v___y_674_ = v___y_693_;
v___y_675_ = v___y_694_;
v___y_676_ = v_vars_722_;
v___y_677_ = v___y_700_;
v___y_678_ = v___y_691_;
v___y_679_ = v___y_692_;
v___y_680_ = v_body_721_;
v___y_681_ = v___y_695_;
v___y_682_ = v___y_697_;
v___y_683_ = v___y_696_;
v___y_684_ = v___y_698_;
v___y_685_ = v___y_699_;
v___y_686_ = v___x_719_;
goto v___jp_671_;
}
else
{
lean_dec_ref(v_s_701_);
v___y_672_ = v___y_690_;
v___y_673_ = v___x_719_;
v___y_674_ = v___y_693_;
v___y_675_ = v___y_694_;
v___y_676_ = v_vars_722_;
v___y_677_ = v___y_700_;
v___y_678_ = v___y_691_;
v___y_679_ = v___y_692_;
v___y_680_ = v_body_721_;
v___y_681_ = v___y_695_;
v___y_682_ = v___y_697_;
v___y_683_ = v___y_696_;
v___y_684_ = v___y_698_;
v___y_685_ = v___y_699_;
v___y_686_ = v___x_704_;
goto v___jp_671_;
}
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v___x_718_);
lean_dec(v_s_701_);
lean_dec(v___y_698_);
lean_dec(v___y_691_);
lean_dec(v___y_690_);
lean_dec(v_stx_424_);
v___x_723_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21);
v___x_724_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___y_699_, v___x_723_, v___y_700_, v___y_697_, v___y_693_, v___y_695_, v___y_694_, v___y_696_);
lean_dec(v___y_699_);
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
v___jp_733_:
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__23));
lean_inc(v_val_735_);
v___x_746_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25));
lean_inc(v_val_735_);
v___x_748_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12));
lean_inc(v_val_735_);
v___x_750_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14));
lean_inc(v_val_735_);
v___x_752_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16));
lean_inc(v_val_735_);
v___x_754_ = l_Lean_Syntax_isOfKind(v_val_735_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_terminationBy_x3f_x3f_738_);
lean_dec(v___y_737_);
lean_dec(v___y_734_);
lean_dec(v_stx_424_);
v___x_755_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_756_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_755_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v_val_735_);
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = l_Lean_Syntax_getArg(v_val_735_, v___y_736_);
v___x_766_ = l_Lean_Syntax_isNone(v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(2u);
v___x_768_ = l_Lean_Syntax_matchesNull(v___x_765_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_terminationBy_x3f_x3f_738_);
lean_dec(v___y_737_);
lean_dec(v___y_734_);
lean_dec(v_stx_424_);
v___x_769_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_770_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_769_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v_val_735_);
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
else
{
lean_dec(v_val_735_);
v___y_660_ = v_terminationBy_x3f_x3f_738_;
v___y_661_ = v___y_734_;
v___y_662_ = v___y_736_;
v___y_663_ = v___y_741_;
v___y_664_ = v___y_743_;
v___y_665_ = v___y_742_;
v___y_666_ = v___y_744_;
v___y_667_ = v___y_740_;
v___y_668_ = v___y_737_;
v___y_669_ = v___y_739_;
goto v___jp_659_;
}
}
else
{
lean_dec(v___x_765_);
lean_dec(v_val_735_);
v___y_660_ = v_terminationBy_x3f_x3f_738_;
v___y_661_ = v___y_734_;
v___y_662_ = v___y_736_;
v___y_663_ = v___y_741_;
v___y_664_ = v___y_743_;
v___y_665_ = v___y_742_;
v___y_666_ = v___y_744_;
v___y_667_ = v___y_740_;
v___y_668_ = v___y_737_;
v___y_669_ = v___y_739_;
goto v___jp_659_;
}
}
}
else
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = l_Lean_Syntax_getArg(v_val_735_, v___y_736_);
v___x_780_ = l_Lean_Syntax_isNone(v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(2u);
v___x_782_ = l_Lean_Syntax_matchesNull(v___x_779_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec(v_terminationBy_x3f_x3f_738_);
lean_dec(v___y_737_);
lean_dec(v___y_734_);
lean_dec(v_stx_424_);
v___x_783_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_784_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_783_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v_val_735_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_dec(v_val_735_);
v___y_648_ = v_terminationBy_x3f_x3f_738_;
v___y_649_ = v___y_734_;
v___y_650_ = v___y_736_;
v___y_651_ = v___y_741_;
v___y_652_ = v___y_743_;
v___y_653_ = v___y_742_;
v___y_654_ = v___y_744_;
v___y_655_ = v___y_740_;
v___y_656_ = v___y_737_;
v___y_657_ = v___y_739_;
goto v___jp_647_;
}
}
else
{
lean_dec(v___x_779_);
lean_dec(v_val_735_);
v___y_648_ = v_terminationBy_x3f_x3f_738_;
v___y_649_ = v___y_734_;
v___y_650_ = v___y_736_;
v___y_651_ = v___y_741_;
v___y_652_ = v___y_743_;
v___y_653_ = v___y_742_;
v___y_654_ = v___y_744_;
v___y_655_ = v___y_740_;
v___y_656_ = v___y_737_;
v___y_657_ = v___y_739_;
goto v___jp_647_;
}
}
}
else
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = l_Lean_Syntax_getArg(v_val_735_, v___y_736_);
v___x_794_ = l_Lean_Syntax_isNone(v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = lean_unsigned_to_nat(2u);
v___x_796_ = l_Lean_Syntax_matchesNull(v___x_793_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_terminationBy_x3f_x3f_738_);
lean_dec(v___y_737_);
lean_dec(v___y_734_);
lean_dec(v_stx_424_);
v___x_797_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_798_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_797_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v_val_735_);
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_dec(v_val_735_);
v___y_636_ = v_terminationBy_x3f_x3f_738_;
v___y_637_ = v___y_734_;
v___y_638_ = v___y_736_;
v___y_639_ = v___y_741_;
v___y_640_ = v___y_743_;
v___y_641_ = v___y_742_;
v___y_642_ = v___y_744_;
v___y_643_ = v___y_740_;
v___y_644_ = v___y_737_;
v___y_645_ = v___y_739_;
goto v___jp_635_;
}
}
else
{
lean_dec(v___x_793_);
lean_dec(v_val_735_);
v___y_636_ = v_terminationBy_x3f_x3f_738_;
v___y_637_ = v___y_734_;
v___y_638_ = v___y_736_;
v___y_639_ = v___y_741_;
v___y_640_ = v___y_743_;
v___y_641_ = v___y_742_;
v___y_642_ = v___y_744_;
v___y_643_ = v___y_740_;
v___y_644_ = v___y_737_;
v___y_645_ = v___y_739_;
goto v___jp_635_;
}
}
}
else
{
lean_object* v___x_807_; 
lean_dec(v___y_734_);
v___x_807_ = lean_box(0);
v___y_561_ = v_terminationBy_x3f_x3f_738_;
v_val_562_ = v_val_735_;
v___y_563_ = v___y_736_;
v___y_564_ = v___y_737_;
v_terminationBy_x3f_565_ = v___x_807_;
v___y_566_ = v___y_739_;
v___y_567_ = v___y_740_;
v___y_568_ = v___y_741_;
v___y_569_ = v___y_742_;
v___y_570_ = v___y_743_;
v___y_571_ = v___y_744_;
goto v___jp_560_;
}
}
else
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = l_Lean_Syntax_getArg(v_val_735_, v___y_736_);
v___x_809_ = l_Lean_Syntax_isNone(v___x_808_);
if (v___x_809_ == 0)
{
uint8_t v___x_810_; 
lean_inc(v___x_808_);
v___x_810_ = l_Lean_Syntax_matchesNull(v___x_808_, v___y_736_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v___x_808_);
lean_dec(v_terminationBy_x3f_x3f_738_);
lean_dec(v___y_737_);
lean_dec(v___y_734_);
lean_dec(v_stx_424_);
v___x_811_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_812_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_val_735_, v___x_811_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v_val_735_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
else
{
lean_object* v_s_821_; lean_object* v___x_822_; 
v_s_821_ = l_Lean_Syntax_getArg(v___x_808_, v___x_458_);
lean_dec(v___x_808_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_s_821_);
v___y_690_ = v_terminationBy_x3f_x3f_738_;
v___y_691_ = v___y_734_;
v___y_692_ = v___y_736_;
v___y_693_ = v___y_741_;
v___y_694_ = v___y_743_;
v___y_695_ = v___y_742_;
v___y_696_ = v___y_744_;
v___y_697_ = v___y_740_;
v___y_698_ = v___y_737_;
v___y_699_ = v_val_735_;
v___y_700_ = v___y_739_;
v_s_701_ = v___x_822_;
goto v___jp_689_;
}
}
else
{
lean_object* v___x_823_; 
lean_dec(v___x_808_);
v___x_823_ = lean_box(0);
v___y_690_ = v_terminationBy_x3f_x3f_738_;
v___y_691_ = v___y_734_;
v___y_692_ = v___y_736_;
v___y_693_ = v___y_741_;
v___y_694_ = v___y_743_;
v___y_695_ = v___y_742_;
v___y_696_ = v___y_744_;
v___y_697_ = v___y_740_;
v___y_698_ = v___y_737_;
v___y_699_ = v_val_735_;
v___y_700_ = v___y_739_;
v_s_701_ = v___x_823_;
goto v___jp_689_;
}
}
}
v___jp_824_:
{
if (lean_obj_tag(v___y_825_) == 1)
{
lean_object* v_val_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_val_828_ = lean_ctor_get(v___y_825_, 0);
lean_inc_n(v_val_828_, 2);
v___x_829_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25));
v___x_830_ = l_Lean_Syntax_isOfKind(v_val_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
v___x_831_ = lean_box(0);
v___y_734_ = v___y_825_;
v_val_735_ = v_val_828_;
v___y_736_ = v___y_826_;
v___y_737_ = v_d_x3f_827_;
v_terminationBy_x3f_x3f_738_ = v___x_831_;
v___y_739_ = v___y_425_;
v___y_740_ = v___y_426_;
v___y_741_ = v___y_427_;
v___y_742_ = v___y_428_;
v___y_743_ = v___y_429_;
v___y_744_ = v___y_430_;
goto v___jp_733_;
}
else
{
lean_object* v___x_832_; 
lean_inc(v_val_828_);
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v_val_828_);
v___y_734_ = v___y_825_;
v_val_735_ = v_val_828_;
v___y_736_ = v___y_826_;
v___y_737_ = v_d_x3f_827_;
v_terminationBy_x3f_x3f_738_ = v___x_832_;
v___y_739_ = v___y_425_;
v___y_740_ = v___y_426_;
v___y_741_ = v___y_427_;
v___y_742_ = v___y_428_;
v___y_743_ = v___y_429_;
v___y_744_ = v___y_430_;
goto v___jp_733_;
}
}
else
{
lean_object* v___x_833_; 
v___x_833_ = lean_box(0);
if (lean_obj_tag(v___y_825_) == 1)
{
lean_object* v_val_834_; 
v_val_834_ = lean_ctor_get(v___y_825_, 0);
lean_inc(v_val_834_);
v___y_734_ = v___y_825_;
v_val_735_ = v_val_834_;
v___y_736_ = v___y_826_;
v___y_737_ = v_d_x3f_827_;
v_terminationBy_x3f_x3f_738_ = v___x_833_;
v___y_739_ = v___y_425_;
v___y_740_ = v___y_426_;
v___y_741_ = v___y_427_;
v___y_742_ = v___y_428_;
v___y_743_ = v___y_429_;
v___y_744_ = v___y_430_;
goto v___jp_733_;
}
else
{
v___y_604_ = v___x_833_;
v___y_605_ = v___y_825_;
v___y_606_ = v___y_826_;
v___y_607_ = v_d_x3f_827_;
v_terminationBy_x3f_608_ = v___x_833_;
v___y_609_ = v___y_425_;
v___y_610_ = v___y_426_;
v___y_611_ = v___y_427_;
v___y_612_ = v___y_428_;
v___y_613_ = v___y_429_;
v___y_614_ = v___y_430_;
goto v___jp_603_;
}
}
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = l_Lean_Syntax_getArg(v_stx_424_, v___x_837_);
v___x_839_ = l_Lean_Syntax_isNone(v___x_838_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; 
lean_inc(v___x_838_);
v___x_840_ = l_Lean_Syntax_matchesNull(v___x_838_, v___x_837_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v___x_838_);
lean_dec(v_t_x3f_836_);
v___x_841_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_842_ = lean_box(0);
lean_inc_n(v_stx_424_, 2);
v___x_843_ = l_Lean_Syntax_formatStx(v_stx_424_, v___x_842_, v___x_840_);
v___x_844_ = l_Std_Format_defWidth;
v___x_845_ = l_Std_Format_pretty(v___x_843_, v___x_844_, v___x_458_, v___x_458_);
v___x_846_ = lean_string_append(v___x_841_, v___x_845_);
lean_dec_ref(v___x_845_);
v___x_847_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_848_ = lean_string_append(v___x_846_, v___x_847_);
v___x_849_ = l_Lean_Syntax_getKind(v_stx_424_);
v___x_850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_849_, v___x_441_);
v___x_851_ = lean_string_append(v___x_848_, v___x_850_);
lean_dec_ref(v___x_850_);
v___x_852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
v___x_853_ = l_Lean_MessageData_ofFormat(v___x_852_);
v___x_854_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_424_, v___x_853_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v_stx_424_);
return v___x_854_;
}
else
{
lean_object* v_d_x3f_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v_d_x3f_855_ = l_Lean_Syntax_getArg(v___x_838_, v___x_458_);
lean_dec(v___x_838_);
v___x_856_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__8));
lean_inc(v_d_x3f_855_);
v___x_857_ = l_Lean_Syntax_isOfKind(v_d_x3f_855_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v_d_x3f_855_);
lean_dec(v_t_x3f_836_);
v___x_858_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__5));
v___x_859_ = lean_box(0);
lean_inc_n(v_stx_424_, 2);
v___x_860_ = l_Lean_Syntax_formatStx(v_stx_424_, v___x_859_, v___x_857_);
v___x_861_ = l_Std_Format_defWidth;
v___x_862_ = l_Std_Format_pretty(v___x_860_, v___x_861_, v___x_458_, v___x_458_);
v___x_863_ = lean_string_append(v___x_858_, v___x_862_);
lean_dec_ref(v___x_862_);
v___x_864_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__6));
v___x_865_ = lean_string_append(v___x_863_, v___x_864_);
v___x_866_ = l_Lean_Syntax_getKind(v_stx_424_);
v___x_867_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_866_, v___x_840_);
v___x_868_ = lean_string_append(v___x_865_, v___x_867_);
lean_dec_ref(v___x_867_);
v___x_869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
v___x_870_ = l_Lean_MessageData_ofFormat(v___x_869_);
v___x_871_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_stx_424_, v___x_870_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v_stx_424_);
return v___x_871_;
}
else
{
lean_object* v___x_872_; 
v___x_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_872_, 0, v_d_x3f_855_);
v___y_825_ = v_t_x3f_836_;
v___y_826_ = v___x_837_;
v_d_x3f_827_ = v___x_872_;
goto v___jp_824_;
}
}
}
else
{
lean_object* v___x_873_; 
lean_dec(v___x_838_);
v___x_873_ = lean_box(0);
v___y_825_ = v_t_x3f_836_;
v___y_826_ = v___x_837_;
v_d_x3f_827_ = v___x_873_;
goto v___jp_824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___boxed(lean_object* v_stx_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(v_stx_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_903_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0(uint8_t v___y_912_, uint8_t v_suppressElabErrors_913_, lean_object* v_x_914_){
_start:
{
if (lean_obj_tag(v_x_914_) == 1)
{
lean_object* v_pre_915_; 
v_pre_915_ = lean_ctor_get(v_x_914_, 0);
switch(lean_obj_tag(v_pre_915_))
{
case 1:
{
lean_object* v_pre_916_; 
v_pre_916_ = lean_ctor_get(v_pre_915_, 0);
switch(lean_obj_tag(v_pre_916_))
{
case 0:
{
lean_object* v_str_917_; lean_object* v_str_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_str_917_ = lean_ctor_get(v_x_914_, 1);
v_str_918_ = lean_ctor_get(v_pre_915_, 1);
v___x_919_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__0));
v___x_920_ = lean_string_dec_eq(v_str_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__1));
v___x_922_ = lean_string_dec_eq(v_str_918_, v___x_921_);
if (v___x_922_ == 0)
{
return v___y_912_;
}
else
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__2));
v___x_924_ = lean_string_dec_eq(v_str_917_, v___x_923_);
if (v___x_924_ == 0)
{
return v___y_912_;
}
else
{
return v_suppressElabErrors_913_;
}
}
}
else
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__3));
v___x_926_ = lean_string_dec_eq(v_str_917_, v___x_925_);
if (v___x_926_ == 0)
{
return v___y_912_;
}
else
{
return v_suppressElabErrors_913_;
}
}
}
case 1:
{
lean_object* v_pre_927_; 
v_pre_927_ = lean_ctor_get(v_pre_916_, 0);
if (lean_obj_tag(v_pre_927_) == 0)
{
lean_object* v_str_928_; lean_object* v_str_929_; lean_object* v_str_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_str_928_ = lean_ctor_get(v_x_914_, 1);
v_str_929_ = lean_ctor_get(v_pre_915_, 1);
v_str_930_ = lean_ctor_get(v_pre_916_, 1);
v___x_931_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__4));
v___x_932_ = lean_string_dec_eq(v_str_930_, v___x_931_);
if (v___x_932_ == 0)
{
return v___y_912_;
}
else
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__5));
v___x_934_ = lean_string_dec_eq(v_str_929_, v___x_933_);
if (v___x_934_ == 0)
{
return v___y_912_;
}
else
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__6));
v___x_936_ = lean_string_dec_eq(v_str_928_, v___x_935_);
if (v___x_936_ == 0)
{
return v___y_912_;
}
else
{
return v_suppressElabErrors_913_;
}
}
}
}
else
{
return v___y_912_;
}
}
default: 
{
return v___y_912_;
}
}
}
case 0:
{
lean_object* v_str_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_str_937_ = lean_ctor_get(v_x_914_, 1);
v___x_938_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___closed__7));
v___x_939_ = lean_string_dec_eq(v_str_937_, v___x_938_);
if (v___x_939_ == 0)
{
return v___y_912_;
}
else
{
return v_suppressElabErrors_913_;
}
}
default: 
{
return v___y_912_;
}
}
}
else
{
return v___y_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___boxed(lean_object* v___y_940_, lean_object* v_suppressElabErrors_941_, lean_object* v_x_942_){
_start:
{
uint8_t v___y_53762__boxed_943_; uint8_t v_suppressElabErrors_boxed_944_; uint8_t v_res_945_; lean_object* v_r_946_; 
v___y_53762__boxed_943_ = lean_unbox(v___y_940_);
v_suppressElabErrors_boxed_944_ = lean_unbox(v_suppressElabErrors_941_);
v_res_945_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0(v___y_53762__boxed_943_, v_suppressElabErrors_boxed_944_, v_x_942_);
lean_dec(v_x_942_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(lean_object* v_ref_948_, lean_object* v_msgData_949_, uint8_t v_severity_950_, uint8_t v_isSilent_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
uint8_t v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; uint8_t v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_995_; uint8_t v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; uint8_t v___y_999_; uint8_t v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1020_; uint8_t v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1024_; uint8_t v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1031_; uint8_t v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; uint8_t v___y_1037_; uint8_t v___x_1042_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; uint8_t v___y_1047_; lean_object* v___y_1048_; uint8_t v___y_1049_; uint8_t v___y_1050_; uint8_t v___y_1052_; uint8_t v___x_1067_; 
v___x_1042_ = 2;
v___x_1067_ = l_Lean_instBEqMessageSeverity_beq(v_severity_950_, v___x_1042_);
if (v___x_1067_ == 0)
{
v___y_1052_ = v___x_1067_;
goto v___jp_1051_;
}
else
{
uint8_t v___x_1068_; 
lean_inc_ref(v_msgData_949_);
v___x_1068_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_949_);
v___y_1052_ = v___x_1068_;
goto v___jp_1051_;
}
v___jp_957_:
{
lean_object* v___x_967_; lean_object* v_currNamespace_968_; lean_object* v_openDecls_969_; lean_object* v_env_970_; lean_object* v_nextMacroScope_971_; lean_object* v_ngen_972_; lean_object* v_auxDeclNGen_973_; lean_object* v_traceState_974_; lean_object* v_cache_975_; lean_object* v_messages_976_; lean_object* v_infoState_977_; lean_object* v_snapshotTasks_978_; lean_object* v_newDecls_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_993_; 
v___x_967_ = lean_st_ref_take(v___y_966_);
v_currNamespace_968_ = lean_ctor_get(v___y_965_, 6);
v_openDecls_969_ = lean_ctor_get(v___y_965_, 7);
v_env_970_ = lean_ctor_get(v___x_967_, 0);
v_nextMacroScope_971_ = lean_ctor_get(v___x_967_, 1);
v_ngen_972_ = lean_ctor_get(v___x_967_, 2);
v_auxDeclNGen_973_ = lean_ctor_get(v___x_967_, 3);
v_traceState_974_ = lean_ctor_get(v___x_967_, 4);
v_cache_975_ = lean_ctor_get(v___x_967_, 5);
v_messages_976_ = lean_ctor_get(v___x_967_, 6);
v_infoState_977_ = lean_ctor_get(v___x_967_, 7);
v_snapshotTasks_978_ = lean_ctor_get(v___x_967_, 8);
v_newDecls_979_ = lean_ctor_get(v___x_967_, 9);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_993_ == 0)
{
v___x_981_ = v___x_967_;
v_isShared_982_ = v_isSharedCheck_993_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_newDecls_979_);
lean_inc(v_snapshotTasks_978_);
lean_inc(v_infoState_977_);
lean_inc(v_messages_976_);
lean_inc(v_cache_975_);
lean_inc(v_traceState_974_);
lean_inc(v_auxDeclNGen_973_);
lean_inc(v_ngen_972_);
lean_inc(v_nextMacroScope_971_);
lean_inc(v_env_970_);
lean_dec(v___x_967_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_993_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
lean_inc(v_openDecls_969_);
lean_inc(v_currNamespace_968_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v_currNamespace_968_);
lean_ctor_set(v___x_983_, 1, v_openDecls_969_);
v___x_984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___y_961_);
lean_inc_ref(v___y_963_);
lean_inc_ref(v___y_960_);
v___x_985_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_985_, 0, v___y_960_);
lean_ctor_set(v___x_985_, 1, v___y_959_);
lean_ctor_set(v___x_985_, 2, v___y_964_);
lean_ctor_set(v___x_985_, 3, v___y_963_);
lean_ctor_set(v___x_985_, 4, v___x_984_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*5, v___y_958_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*5 + 1, v___y_962_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*5 + 2, v_isSilent_951_);
v___x_986_ = l_Lean_MessageLog_add(v___x_985_, v_messages_976_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 6, v___x_986_);
v___x_988_ = v___x_981_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_env_970_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_nextMacroScope_971_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_ngen_972_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v_auxDeclNGen_973_);
lean_ctor_set(v_reuseFailAlloc_992_, 4, v_traceState_974_);
lean_ctor_set(v_reuseFailAlloc_992_, 5, v_cache_975_);
lean_ctor_set(v_reuseFailAlloc_992_, 6, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_992_, 7, v_infoState_977_);
lean_ctor_set(v_reuseFailAlloc_992_, 8, v_snapshotTasks_978_);
lean_ctor_set(v_reuseFailAlloc_992_, 9, v_newDecls_979_);
v___x_988_ = v_reuseFailAlloc_992_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_st_ref_set(v___y_966_, v___x_988_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
}
v___jp_994_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1018_; 
v___x_1003_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_949_);
v___x_1004_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16(v___x_1003_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_inc_ref_n(v___y_998_, 2);
v___x_1009_ = l_Lean_FileMap_toPosition(v___y_998_, v___y_1001_);
lean_dec(v___y_1001_);
v___x_1010_ = l_Lean_FileMap_toPosition(v___y_998_, v___y_1002_);
lean_dec(v___y_1002_);
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
v___x_1012_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0));
if (v___y_999_ == 0)
{
lean_del_object(v___x_1007_);
lean_dec_ref(v___y_995_);
v___y_958_ = v___y_996_;
v___y_959_ = v___x_1009_;
v___y_960_ = v___y_997_;
v___y_961_ = v_a_1005_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___x_1012_;
v___y_964_ = v___x_1011_;
v___y_965_ = v___y_954_;
v___y_966_ = v___y_955_;
goto v___jp_957_;
}
else
{
uint8_t v___x_1013_; 
lean_inc(v_a_1005_);
v___x_1013_ = l_Lean_MessageData_hasTag(v___y_995_, v_a_1005_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec_ref(v___x_1011_);
lean_dec_ref(v___x_1009_);
lean_dec(v_a_1005_);
v___x_1014_ = lean_box(0);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1014_);
v___x_1016_ = v___x_1007_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_del_object(v___x_1007_);
v___y_958_ = v___y_996_;
v___y_959_ = v___x_1009_;
v___y_960_ = v___y_997_;
v___y_961_ = v_a_1005_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___x_1012_;
v___y_964_ = v___x_1011_;
v___y_965_ = v___y_954_;
v___y_966_ = v___y_955_;
goto v___jp_957_;
}
}
}
}
v___jp_1019_:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_Syntax_getTailPos_x3f(v___y_1026_, v___y_1021_);
lean_dec(v___y_1026_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_inc(v___y_1027_);
v___y_995_ = v___y_1020_;
v___y_996_ = v___y_1021_;
v___y_997_ = v___y_1022_;
v___y_998_ = v___y_1023_;
v___y_999_ = v___y_1024_;
v___y_1000_ = v___y_1025_;
v___y_1001_ = v___y_1027_;
v___y_1002_ = v___y_1027_;
goto v___jp_994_;
}
else
{
lean_object* v_val_1029_; 
v_val_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_val_1029_);
lean_dec_ref(v___x_1028_);
v___y_995_ = v___y_1020_;
v___y_996_ = v___y_1021_;
v___y_997_ = v___y_1022_;
v___y_998_ = v___y_1023_;
v___y_999_ = v___y_1024_;
v___y_1000_ = v___y_1025_;
v___y_1001_ = v___y_1027_;
v___y_1002_ = v_val_1029_;
goto v___jp_994_;
}
}
v___jp_1030_:
{
lean_object* v_ref_1038_; lean_object* v___x_1039_; 
v_ref_1038_ = l_Lean_replaceRef(v_ref_948_, v___y_1035_);
v___x_1039_ = l_Lean_Syntax_getPos_x3f(v_ref_1038_, v___y_1032_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_unsigned_to_nat(0u);
v___y_1020_ = v___y_1031_;
v___y_1021_ = v___y_1032_;
v___y_1022_ = v___y_1033_;
v___y_1023_ = v___y_1034_;
v___y_1024_ = v___y_1036_;
v___y_1025_ = v___y_1037_;
v___y_1026_ = v_ref_1038_;
v___y_1027_ = v___x_1040_;
goto v___jp_1019_;
}
else
{
lean_object* v_val_1041_; 
v_val_1041_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_val_1041_);
lean_dec_ref(v___x_1039_);
v___y_1020_ = v___y_1031_;
v___y_1021_ = v___y_1032_;
v___y_1022_ = v___y_1033_;
v___y_1023_ = v___y_1034_;
v___y_1024_ = v___y_1036_;
v___y_1025_ = v___y_1037_;
v___y_1026_ = v_ref_1038_;
v___y_1027_ = v_val_1041_;
goto v___jp_1019_;
}
}
v___jp_1043_:
{
if (v___y_1050_ == 0)
{
v___y_1031_ = v___y_1048_;
v___y_1032_ = v___y_1049_;
v___y_1033_ = v___y_1044_;
v___y_1034_ = v___y_1046_;
v___y_1035_ = v___y_1045_;
v___y_1036_ = v___y_1047_;
v___y_1037_ = v_severity_950_;
goto v___jp_1030_;
}
else
{
v___y_1031_ = v___y_1048_;
v___y_1032_ = v___y_1049_;
v___y_1033_ = v___y_1044_;
v___y_1034_ = v___y_1046_;
v___y_1035_ = v___y_1045_;
v___y_1036_ = v___y_1047_;
v___y_1037_ = v___x_1042_;
goto v___jp_1030_;
}
}
v___jp_1051_:
{
if (v___y_1052_ == 0)
{
lean_object* v_fileName_1053_; lean_object* v_fileMap_1054_; lean_object* v_options_1055_; lean_object* v_ref_1056_; uint8_t v_suppressElabErrors_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___f_1060_; uint8_t v___x_1061_; uint8_t v___x_1062_; 
v_fileName_1053_ = lean_ctor_get(v___y_954_, 0);
v_fileMap_1054_ = lean_ctor_get(v___y_954_, 1);
v_options_1055_ = lean_ctor_get(v___y_954_, 2);
v_ref_1056_ = lean_ctor_get(v___y_954_, 5);
v_suppressElabErrors_1057_ = lean_ctor_get_uint8(v___y_954_, sizeof(void*)*14 + 1);
v___x_1058_ = lean_box(v___y_1052_);
v___x_1059_ = lean_box(v_suppressElabErrors_1057_);
v___f_1060_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1060_, 0, v___x_1058_);
lean_closure_set(v___f_1060_, 1, v___x_1059_);
v___x_1061_ = 1;
v___x_1062_ = l_Lean_instBEqMessageSeverity_beq(v_severity_950_, v___x_1061_);
if (v___x_1062_ == 0)
{
v___y_1044_ = v_fileName_1053_;
v___y_1045_ = v_ref_1056_;
v___y_1046_ = v_fileMap_1054_;
v___y_1047_ = v_suppressElabErrors_1057_;
v___y_1048_ = v___f_1060_;
v___y_1049_ = v___y_1052_;
v___y_1050_ = v___x_1062_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = l_Lean_warningAsError;
v___x_1064_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_options_1055_, v___x_1063_);
v___y_1044_ = v_fileName_1053_;
v___y_1045_ = v_ref_1056_;
v___y_1046_ = v_fileMap_1054_;
v___y_1047_ = v_suppressElabErrors_1057_;
v___y_1048_ = v___f_1060_;
v___y_1049_ = v___y_1052_;
v___y_1050_ = v___x_1064_;
goto v___jp_1043_;
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref(v_msgData_949_);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___boxed(lean_object* v_ref_1069_, lean_object* v_msgData_1070_, lean_object* v_severity_1071_, lean_object* v_isSilent_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
uint8_t v_severity_boxed_1078_; uint8_t v_isSilent_boxed_1079_; lean_object* v_res_1080_; 
v_severity_boxed_1078_ = lean_unbox(v_severity_1071_);
v_isSilent_boxed_1079_ = lean_unbox(v_isSilent_1072_);
v_res_1080_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(v_ref_1069_, v_msgData_1070_, v_severity_boxed_1078_, v_isSilent_boxed_1079_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_ref_1069_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44(lean_object* v_msgData_1081_, uint8_t v_severity_1082_, uint8_t v_isSilent_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_ref_1091_; lean_object* v___x_1092_; 
v_ref_1091_ = lean_ctor_get(v___y_1088_, 5);
v___x_1092_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(v_ref_1091_, v_msgData_1081_, v_severity_1082_, v_isSilent_1083_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44___boxed(lean_object* v_msgData_1093_, lean_object* v_severity_1094_, lean_object* v_isSilent_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v_severity_boxed_1103_; uint8_t v_isSilent_boxed_1104_; lean_object* v_res_1105_; 
v_severity_boxed_1103_ = lean_unbox(v_severity_1094_);
v_isSilent_boxed_1104_ = lean_unbox(v_isSilent_1095_);
v_res_1105_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44(v_msgData_1093_, v_severity_boxed_1103_, v_isSilent_boxed_1104_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39(lean_object* v_msgData_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
uint8_t v___x_1114_; uint8_t v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = 2;
v___x_1115_ = 0;
v___x_1116_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39_spec__44(v_msgData_1106_, v___x_1114_, v___x_1115_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39___boxed(lean_object* v_msgData_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39(v_msgData_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38(lean_object* v_ref_1126_, lean_object* v_msgData_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
uint8_t v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = 2;
v___x_1136_ = 0;
v___x_1137_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(v_ref_1126_, v_msgData_1127_, v___x_1135_, v___x_1136_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38___boxed(lean_object* v_ref_1138_, lean_object* v_msgData_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38(v_ref_1138_, v_msgData_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v_ref_1138_);
return v_res_1147_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__0));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32(lean_object* v_ex_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
if (lean_obj_tag(v_ex_1151_) == 0)
{
lean_object* v_ref_1159_; lean_object* v_msg_1160_; lean_object* v___x_1161_; 
v_ref_1159_ = lean_ctor_get(v_ex_1151_, 0);
lean_inc(v_ref_1159_);
v_msg_1160_ = lean_ctor_get(v_ex_1151_, 1);
lean_inc_ref(v_msg_1160_);
lean_dec_ref(v_ex_1151_);
v___x_1161_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38(v_ref_1159_, v_msg_1160_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v_ref_1159_);
return v___x_1161_;
}
else
{
lean_object* v_id_1162_; uint8_t v___y_1164_; uint8_t v___x_1186_; 
v_id_1162_ = lean_ctor_get(v_ex_1151_, 0);
lean_inc(v_id_1162_);
v___x_1186_ = l_Lean_Elab_isAbortExceptionId(v_id_1162_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; 
v___x_1187_ = l_Lean_Exception_isInterrupt(v_ex_1151_);
lean_dec_ref(v_ex_1151_);
v___y_1164_ = v___x_1187_;
goto v___jp_1163_;
}
else
{
lean_dec_ref(v_ex_1151_);
v___y_1164_ = v___x_1186_;
goto v___jp_1163_;
}
v___jp_1163_:
{
if (v___y_1164_ == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_InternalExceptionId_getName(v_id_1162_);
lean_dec(v_id_1162_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___closed__1);
v___x_1168_ = l_Lean_MessageData_ofName(v_a_1166_);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__39(v___x_1169_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1170_;
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1183_; 
v_a_1171_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1173_ = v___x_1165_;
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1165_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1183_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_ref_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v_ref_1175_ = lean_ctor_get(v___y_1156_, 5);
v___x_1176_ = lean_io_error_to_string(v_a_1171_);
v___x_1177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
v___x_1178_ = l_Lean_MessageData_ofFormat(v___x_1177_);
lean_inc(v_ref_1175_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_ref_1175_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1179_);
v___x_1181_ = v___x_1173_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_dec(v_id_1162_);
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32___boxed(lean_object* v_ex_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32(v_ex_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1196_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0(lean_object* v_k_1204_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___closed__2));
v___x_1206_ = lean_name_eq(v_k_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
uint8_t v___x_1207_; 
v___x_1207_ = 1;
return v___x_1207_;
}
else
{
uint8_t v___x_1208_; 
v___x_1208_ = 0;
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0___boxed(lean_object* v_k_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__0(v_k_1209_);
lean_dec(v_k_1209_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(lean_object* v_keys_1212_, lean_object* v_i_1213_, lean_object* v_k_1214_){
_start:
{
lean_object* v___x_1215_; uint8_t v___x_1216_; 
v___x_1215_ = lean_array_get_size(v_keys_1212_);
v___x_1216_ = lean_nat_dec_lt(v_i_1213_, v___x_1215_);
if (v___x_1216_ == 0)
{
lean_dec(v_i_1213_);
return v___x_1216_;
}
else
{
lean_object* v_k_x27_1217_; uint8_t v___x_1218_; 
v_k_x27_1217_ = lean_array_fget_borrowed(v_keys_1212_, v_i_1213_);
v___x_1218_ = l_Lean_instBEqExtraModUse_beq(v_k_1214_, v_k_x27_1217_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_nat_add(v_i_1213_, v___x_1219_);
lean_dec(v_i_1213_);
v_i_1213_ = v___x_1220_;
goto _start;
}
else
{
lean_dec(v_i_1213_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg___boxed(lean_object* v_keys_1222_, lean_object* v_i_1223_, lean_object* v_k_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(v_keys_1222_, v_i_1223_, v_k_1224_);
lean_dec_ref(v_k_1224_);
lean_dec_ref(v_keys_1222_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0(void){
_start:
{
size_t v___x_1227_; size_t v___x_1228_; size_t v___x_1229_; 
v___x_1227_ = ((size_t)5ULL);
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_shift_left(v___x_1228_, v___x_1227_);
return v___x_1229_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1(void){
_start:
{
size_t v___x_1230_; size_t v___x_1231_; size_t v___x_1232_; 
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0);
v___x_1232_ = lean_usize_sub(v___x_1231_, v___x_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(lean_object* v_x_1233_, size_t v_x_1234_, lean_object* v_x_1235_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
lean_object* v_es_1236_; lean_object* v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; lean_object* v_j_1241_; lean_object* v___x_1242_; 
v_es_1236_ = lean_ctor_get(v_x_1233_, 0);
v___x_1237_ = lean_box(2);
v___x_1238_ = ((size_t)5ULL);
v___x_1239_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1);
v___x_1240_ = lean_usize_land(v_x_1234_, v___x_1239_);
v_j_1241_ = lean_usize_to_nat(v___x_1240_);
v___x_1242_ = lean_array_get_borrowed(v___x_1237_, v_es_1236_, v_j_1241_);
lean_dec(v_j_1241_);
switch(lean_obj_tag(v___x_1242_))
{
case 0:
{
lean_object* v_key_1243_; uint8_t v___x_1244_; 
v_key_1243_ = lean_ctor_get(v___x_1242_, 0);
v___x_1244_ = l_Lean_instBEqExtraModUse_beq(v_x_1235_, v_key_1243_);
return v___x_1244_;
}
case 1:
{
lean_object* v_node_1245_; size_t v___x_1246_; 
v_node_1245_ = lean_ctor_get(v___x_1242_, 0);
v___x_1246_ = lean_usize_shift_right(v_x_1234_, v___x_1238_);
v_x_1233_ = v_node_1245_;
v_x_1234_ = v___x_1246_;
goto _start;
}
default: 
{
uint8_t v___x_1248_; 
v___x_1248_ = 0;
return v___x_1248_;
}
}
}
else
{
lean_object* v_ks_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_ks_1249_ = lean_ctor_get(v_x_1233_, 0);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(v_ks_1249_, v___x_1250_, v_x_1235_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___boxed(lean_object* v_x_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
size_t v_x_54261__boxed_1255_; uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_x_54261__boxed_1255_ = lean_unbox_usize(v_x_1253_);
lean_dec(v_x_1253_);
v_res_1256_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(v_x_1252_, v_x_54261__boxed_1255_, v_x_1254_);
lean_dec_ref(v_x_1254_);
lean_dec_ref(v_x_1252_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
uint64_t v___x_1260_; size_t v___x_1261_; uint8_t v___x_1262_; 
v___x_1260_ = l_Lean_instHashableExtraModUse_hash(v_x_1259_);
v___x_1261_ = lean_uint64_to_usize(v___x_1260_);
v___x_1262_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(v_x_1258_, v___x_1261_, v_x_1259_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg___boxed(lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_res_1265_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(v_x_1263_, v_x_1264_);
lean_dec_ref(v_x_1264_);
lean_dec_ref(v_x_1263_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1267_; double v___x_1268_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_float_of_nat(v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(lean_object* v_cls_1271_, lean_object* v_msg_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_ref_1278_; lean_object* v___x_1279_; lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1325_; 
v_ref_1278_ = lean_ctor_get(v___y_1275_, 5);
v___x_1279_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16(v_msg_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1325_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1325_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v_traceState_1285_; lean_object* v_env_1286_; lean_object* v_nextMacroScope_1287_; lean_object* v_ngen_1288_; lean_object* v_auxDeclNGen_1289_; lean_object* v_cache_1290_; lean_object* v_messages_1291_; lean_object* v_infoState_1292_; lean_object* v_snapshotTasks_1293_; lean_object* v_newDecls_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1324_; 
v___x_1284_ = lean_st_ref_take(v___y_1276_);
v_traceState_1285_ = lean_ctor_get(v___x_1284_, 4);
v_env_1286_ = lean_ctor_get(v___x_1284_, 0);
v_nextMacroScope_1287_ = lean_ctor_get(v___x_1284_, 1);
v_ngen_1288_ = lean_ctor_get(v___x_1284_, 2);
v_auxDeclNGen_1289_ = lean_ctor_get(v___x_1284_, 3);
v_cache_1290_ = lean_ctor_get(v___x_1284_, 5);
v_messages_1291_ = lean_ctor_get(v___x_1284_, 6);
v_infoState_1292_ = lean_ctor_get(v___x_1284_, 7);
v_snapshotTasks_1293_ = lean_ctor_get(v___x_1284_, 8);
v_newDecls_1294_ = lean_ctor_get(v___x_1284_, 9);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1296_ = v___x_1284_;
v_isShared_1297_ = v_isSharedCheck_1324_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_newDecls_1294_);
lean_inc(v_snapshotTasks_1293_);
lean_inc(v_infoState_1292_);
lean_inc(v_messages_1291_);
lean_inc(v_cache_1290_);
lean_inc(v_traceState_1285_);
lean_inc(v_auxDeclNGen_1289_);
lean_inc(v_ngen_1288_);
lean_inc(v_nextMacroScope_1287_);
lean_inc(v_env_1286_);
lean_dec(v___x_1284_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1324_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
uint64_t v_tid_1298_; lean_object* v_traces_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1323_; 
v_tid_1298_ = lean_ctor_get_uint64(v_traceState_1285_, sizeof(void*)*1);
v_traces_1299_ = lean_ctor_get(v_traceState_1285_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_traceState_1285_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1301_ = v_traceState_1285_;
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_traces_1299_);
lean_dec(v_traceState_1285_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; double v___x_1304_; uint8_t v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0);
v___x_1305_ = 0;
v___x_1306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0));
v___x_1307_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1307_, 0, v_cls_1271_);
lean_ctor_set(v___x_1307_, 1, v___x_1303_);
lean_ctor_set(v___x_1307_, 2, v___x_1306_);
lean_ctor_set_float(v___x_1307_, sizeof(void*)*3, v___x_1304_);
lean_ctor_set_float(v___x_1307_, sizeof(void*)*3 + 8, v___x_1304_);
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*3 + 16, v___x_1305_);
v___x_1308_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1));
v___x_1309_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v_a_1280_);
lean_ctor_set(v___x_1309_, 2, v___x_1308_);
lean_inc(v_ref_1278_);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_ref_1278_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
v___x_1311_ = l_Lean_PersistentArray_push___redArg(v_traces_1299_, v___x_1310_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1311_);
v___x_1313_ = v___x_1301_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1311_);
lean_ctor_set_uint64(v_reuseFailAlloc_1322_, sizeof(void*)*1, v_tid_1298_);
v___x_1313_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 4, v___x_1313_);
v___x_1315_ = v___x_1296_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_env_1286_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_nextMacroScope_1287_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_ngen_1288_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_auxDeclNGen_1289_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v_cache_1290_);
lean_ctor_set(v_reuseFailAlloc_1321_, 6, v_messages_1291_);
lean_ctor_set(v_reuseFailAlloc_1321_, 7, v_infoState_1292_);
lean_ctor_set(v_reuseFailAlloc_1321_, 8, v_snapshotTasks_1293_);
lean_ctor_set(v_reuseFailAlloc_1321_, 9, v_newDecls_1294_);
v___x_1315_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1316_ = lean_st_ref_set(v___y_1276_, v___x_1315_);
v___x_1317_ = lean_box(0);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1317_);
v___x_1319_ = v___x_1282_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___boxed(lean_object* v_cls_1326_, lean_object* v_msg_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_1326_, v_msg_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1333_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__1));
v___x_1337_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__0));
v___x_1338_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1337_, v___x_1336_);
return v___x_1338_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__5));
v___x_1344_ = l_Lean_stringToMessageData(v___x_1343_);
return v___x_1344_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__7));
v___x_1347_ = l_Lean_stringToMessageData(v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0));
v___x_1349_ = l_Lean_stringToMessageData(v___x_1348_);
return v___x_1349_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11(void){
_start:
{
lean_object* v_cls_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_cls_1352_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__4));
v___x_1353_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__10));
v___x_1354_ = l_Lean_Name_append(v___x_1353_, v_cls_1352_);
return v___x_1354_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__12));
v___x_1357_ = l_Lean_stringToMessageData(v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15(void){
_start:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__14));
v___x_1360_ = l_Lean_stringToMessageData(v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(lean_object* v_mod_1365_, uint8_t v_isMeta_1366_, lean_object* v_hint_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; lean_object* v_env_1376_; uint8_t v_isExporting_1377_; lean_object* v___x_1378_; lean_object* v_env_1379_; lean_object* v___x_1380_; lean_object* v_entry_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1375_ = lean_st_ref_get(v___y_1373_);
v_env_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_ref(v_env_1376_);
lean_dec(v___x_1375_);
v_isExporting_1377_ = lean_ctor_get_uint8(v_env_1376_, sizeof(void*)*8);
lean_dec_ref(v_env_1376_);
v___x_1378_ = lean_st_ref_get(v___y_1373_);
v_env_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc_ref(v_env_1379_);
lean_dec(v___x_1378_);
v___x_1380_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2);
lean_inc(v_mod_1365_);
v_entry_1381_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1381_, 0, v_mod_1365_);
lean_ctor_set_uint8(v_entry_1381_, sizeof(void*)*1, v_isExporting_1377_);
lean_ctor_set_uint8(v_entry_1381_, sizeof(void*)*1 + 1, v_isMeta_1366_);
v___x_1382_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1383_ = lean_box(1);
v___x_1384_ = lean_box(0);
v___x_1428_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1380_, v___x_1382_, v_env_1379_, v___x_1383_, v___x_1384_);
v___x_1429_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(v___x_1428_, v_entry_1381_);
lean_dec(v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v_options_1430_; uint8_t v_hasTrace_1431_; 
v_options_1430_ = lean_ctor_get(v___y_1372_, 2);
v_hasTrace_1431_ = lean_ctor_get_uint8(v_options_1430_, sizeof(void*)*1);
if (v_hasTrace_1431_ == 0)
{
lean_dec(v_hint_1367_);
lean_dec(v_mod_1365_);
v___y_1386_ = v___y_1371_;
v___y_1387_ = v___y_1373_;
goto v___jp_1385_;
}
else
{
lean_object* v_inheritedTraceOptions_1432_; lean_object* v_cls_1433_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_inheritedTraceOptions_1432_ = lean_ctor_get(v___y_1372_, 13);
v_cls_1433_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__4));
v___x_1453_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11);
v___x_1454_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1432_, v_options_1430_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_dec(v_hint_1367_);
lean_dec(v_mod_1365_);
v___y_1386_ = v___y_1371_;
v___y_1387_ = v___y_1373_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1455_; lean_object* v___y_1457_; 
v___x_1455_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13);
if (v_isExporting_1377_ == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__18));
v___y_1457_ = v___x_1464_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1465_; 
v___x_1465_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__19));
v___y_1457_ = v___x_1465_;
goto v___jp_1456_;
}
v___jp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_inc_ref(v___y_1457_);
v___x_1458_ = l_Lean_stringToMessageData(v___y_1457_);
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1455_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15);
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
if (v_isMeta_1366_ == 0)
{
lean_object* v___x_1462_; 
v___x_1462_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__16));
v___y_1440_ = v___x_1461_;
v___y_1441_ = v___x_1462_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1463_; 
v___x_1463_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__17));
v___y_1440_ = v___x_1461_;
v___y_1441_ = v___x_1463_;
goto v___jp_1439_;
}
}
}
v___jp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___y_1435_);
lean_ctor_set(v___x_1437_, 1, v___y_1436_);
v___x_1438_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_1433_, v___x_1437_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref(v___x_1438_);
v___y_1386_ = v___y_1371_;
v___y_1387_ = v___y_1373_;
goto v___jp_1385_;
}
else
{
lean_dec_ref(v_entry_1381_);
return v___x_1438_;
}
}
v___jp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
lean_inc_ref(v___y_1441_);
v___x_1442_ = l_Lean_stringToMessageData(v___y_1441_);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___y_1440_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = l_Lean_MessageData_ofName(v_mod_1365_);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_Name_isAnonymous(v_hint_1367_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8);
v___x_1450_ = l_Lean_MessageData_ofName(v_hint_1367_);
v___x_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___y_1435_ = v___x_1447_;
v___y_1436_ = v___x_1451_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1452_; 
lean_dec(v_hint_1367_);
v___x_1452_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9);
v___y_1435_ = v___x_1447_;
v___y_1436_ = v___x_1452_;
goto v___jp_1434_;
}
}
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_entry_1381_);
lean_dec(v_hint_1367_);
lean_dec(v_mod_1365_);
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
v___jp_1385_:
{
lean_object* v___x_1388_; lean_object* v_toEnvExtension_1389_; lean_object* v_env_1390_; lean_object* v_nextMacroScope_1391_; lean_object* v_ngen_1392_; lean_object* v_auxDeclNGen_1393_; lean_object* v_traceState_1394_; lean_object* v_messages_1395_; lean_object* v_infoState_1396_; lean_object* v_snapshotTasks_1397_; lean_object* v_newDecls_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1426_; 
v___x_1388_ = lean_st_ref_take(v___y_1387_);
v_toEnvExtension_1389_ = lean_ctor_get(v___x_1382_, 0);
v_env_1390_ = lean_ctor_get(v___x_1388_, 0);
v_nextMacroScope_1391_ = lean_ctor_get(v___x_1388_, 1);
v_ngen_1392_ = lean_ctor_get(v___x_1388_, 2);
v_auxDeclNGen_1393_ = lean_ctor_get(v___x_1388_, 3);
v_traceState_1394_ = lean_ctor_get(v___x_1388_, 4);
v_messages_1395_ = lean_ctor_get(v___x_1388_, 6);
v_infoState_1396_ = lean_ctor_get(v___x_1388_, 7);
v_snapshotTasks_1397_ = lean_ctor_get(v___x_1388_, 8);
v_newDecls_1398_ = lean_ctor_get(v___x_1388_, 9);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v___x_1388_, 5);
lean_dec(v_unused_1427_);
v___x_1400_ = v___x_1388_;
v_isShared_1401_ = v_isSharedCheck_1426_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_newDecls_1398_);
lean_inc(v_snapshotTasks_1397_);
lean_inc(v_infoState_1396_);
lean_inc(v_messages_1395_);
lean_inc(v_traceState_1394_);
lean_inc(v_auxDeclNGen_1393_);
lean_inc(v_ngen_1392_);
lean_inc(v_nextMacroScope_1391_);
lean_inc(v_env_1390_);
lean_dec(v___x_1388_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1426_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_asyncMode_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v_asyncMode_1402_ = lean_ctor_get(v_toEnvExtension_1389_, 2);
v___x_1403_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1382_, v_env_1390_, v_entry_1381_, v_asyncMode_1402_, v___x_1384_);
v___x_1404_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 5, v___x_1404_);
lean_ctor_set(v___x_1400_, 0, v___x_1403_);
v___x_1406_ = v___x_1400_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_nextMacroScope_1391_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_ngen_1392_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_auxDeclNGen_1393_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_traceState_1394_);
lean_ctor_set(v_reuseFailAlloc_1425_, 5, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1425_, 6, v_messages_1395_);
lean_ctor_set(v_reuseFailAlloc_1425_, 7, v_infoState_1396_);
lean_ctor_set(v_reuseFailAlloc_1425_, 8, v_snapshotTasks_1397_);
lean_ctor_set(v_reuseFailAlloc_1425_, 9, v_newDecls_1398_);
v___x_1406_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_mctx_1409_; lean_object* v_zetaDeltaFVarIds_1410_; lean_object* v_postponed_1411_; lean_object* v_diag_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1423_; 
v___x_1407_ = lean_st_ref_set(v___y_1387_, v___x_1406_);
v___x_1408_ = lean_st_ref_take(v___y_1386_);
v_mctx_1409_ = lean_ctor_get(v___x_1408_, 0);
v_zetaDeltaFVarIds_1410_ = lean_ctor_get(v___x_1408_, 2);
v_postponed_1411_ = lean_ctor_get(v___x_1408_, 3);
v_diag_1412_ = lean_ctor_get(v___x_1408_, 4);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v___x_1408_, 1);
lean_dec(v_unused_1424_);
v___x_1414_ = v___x_1408_;
v_isShared_1415_ = v_isSharedCheck_1423_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_diag_1412_);
lean_inc(v_postponed_1411_);
lean_inc(v_zetaDeltaFVarIds_1410_);
lean_inc(v_mctx_1409_);
lean_dec(v___x_1408_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1423_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1416_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v___x_1416_);
v___x_1418_ = v___x_1414_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_mctx_1409_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_zetaDeltaFVarIds_1410_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_postponed_1411_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_diag_1412_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_st_ref_set(v___y_1386_, v___x_1418_);
v___x_1420_ = lean_box(0);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___boxed(lean_object* v_mod_1468_, lean_object* v_isMeta_1469_, lean_object* v_hint_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
uint8_t v_isMeta_boxed_1478_; lean_object* v_res_1479_; 
v_isMeta_boxed_1478_ = lean_unbox(v_isMeta_1469_);
v_res_1479_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(v_mod_1468_, v_isMeta_boxed_1478_, v_hint_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(lean_object* v___x_1480_, lean_object* v_declName_1481_, lean_object* v_as_1482_, size_t v_sz_1483_, size_t v_i_1484_, lean_object* v_b_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
uint8_t v___x_1493_; 
v___x_1493_ = lean_usize_dec_lt(v_i_1484_, v_sz_1483_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; 
lean_dec(v_declName_1481_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_b_1485_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; lean_object* v_modules_1496_; lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v_toImport_1500_; lean_object* v_module_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; 
v___x_1495_ = l_Lean_Environment_header(v___x_1480_);
v_modules_1496_ = lean_ctor_get(v___x_1495_, 3);
lean_inc_ref(v_modules_1496_);
lean_dec_ref(v___x_1495_);
v___x_1497_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1498_ = lean_array_uget_borrowed(v_as_1482_, v_i_1484_);
v___x_1499_ = lean_array_get(v___x_1497_, v_modules_1496_, v_a_1498_);
lean_dec_ref(v_modules_1496_);
v_toImport_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc_ref(v_toImport_1500_);
lean_dec(v___x_1499_);
v_module_1501_ = lean_ctor_get(v_toImport_1500_, 0);
lean_inc(v_module_1501_);
lean_dec_ref(v_toImport_1500_);
v___x_1502_ = 0;
lean_inc(v_declName_1481_);
v___x_1503_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(v_module_1501_, v___x_1502_, v_declName_1481_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; 
lean_dec_ref(v___x_1503_);
v___x_1504_ = lean_box(0);
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_add(v_i_1484_, v___x_1505_);
v_i_1484_ = v___x_1506_;
v_b_1485_ = v___x_1504_;
goto _start;
}
else
{
lean_dec(v_declName_1481_);
return v___x_1503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18___boxed(lean_object* v___x_1508_, lean_object* v_declName_1509_, lean_object* v_as_1510_, lean_object* v_sz_1511_, lean_object* v_i_1512_, lean_object* v_b_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
size_t v_sz_boxed_1521_; size_t v_i_boxed_1522_; lean_object* v_res_1523_; 
v_sz_boxed_1521_ = lean_unbox_usize(v_sz_1511_);
lean_dec(v_sz_1511_);
v_i_boxed_1522_ = lean_unbox_usize(v_i_1512_);
lean_dec(v_i_1512_);
v_res_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(v___x_1508_, v_declName_1509_, v_as_1510_, v_sz_boxed_1521_, v_i_boxed_1522_, v_b_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec_ref(v_as_1510_);
lean_dec_ref(v___x_1508_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(lean_object* v_a_1524_, lean_object* v_x_1525_){
_start:
{
if (lean_obj_tag(v_x_1525_) == 0)
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_box(0);
return v___x_1526_;
}
else
{
lean_object* v_key_1527_; lean_object* v_value_1528_; lean_object* v_tail_1529_; uint8_t v___x_1530_; 
v_key_1527_ = lean_ctor_get(v_x_1525_, 0);
v_value_1528_ = lean_ctor_get(v_x_1525_, 1);
v_tail_1529_ = lean_ctor_get(v_x_1525_, 2);
v___x_1530_ = lean_name_eq(v_key_1527_, v_a_1524_);
if (v___x_1530_ == 0)
{
v_x_1525_ = v_tail_1529_;
goto _start;
}
else
{
lean_object* v___x_1532_; 
lean_inc(v_value_1528_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v_value_1528_);
return v___x_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg___boxed(lean_object* v_a_1533_, lean_object* v_x_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(v_a_1533_, v_x_1534_);
lean_dec(v_x_1534_);
lean_dec(v_a_1533_);
return v_res_1535_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1536_; uint64_t v___x_1537_; 
v___x_1536_ = lean_unsigned_to_nat(1723u);
v___x_1537_ = lean_uint64_of_nat(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(lean_object* v_m_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_buckets_1540_; lean_object* v___x_1541_; uint64_t v___y_1543_; 
v_buckets_1540_ = lean_ctor_get(v_m_1538_, 1);
v___x_1541_ = lean_array_get_size(v_buckets_1540_);
if (lean_obj_tag(v_a_1539_) == 0)
{
uint64_t v___x_1557_; 
v___x_1557_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0);
v___y_1543_ = v___x_1557_;
goto v___jp_1542_;
}
else
{
uint64_t v_hash_1558_; 
v_hash_1558_ = lean_ctor_get_uint64(v_a_1539_, sizeof(void*)*2);
v___y_1543_ = v_hash_1558_;
goto v___jp_1542_;
}
v___jp_1542_:
{
uint64_t v___x_1544_; uint64_t v___x_1545_; uint64_t v_fold_1546_; uint64_t v___x_1547_; uint64_t v___x_1548_; uint64_t v___x_1549_; size_t v___x_1550_; size_t v___x_1551_; size_t v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1544_ = 32ULL;
v___x_1545_ = lean_uint64_shift_right(v___y_1543_, v___x_1544_);
v_fold_1546_ = lean_uint64_xor(v___y_1543_, v___x_1545_);
v___x_1547_ = 16ULL;
v___x_1548_ = lean_uint64_shift_right(v_fold_1546_, v___x_1547_);
v___x_1549_ = lean_uint64_xor(v_fold_1546_, v___x_1548_);
v___x_1550_ = lean_uint64_to_usize(v___x_1549_);
v___x_1551_ = lean_usize_of_nat(v___x_1541_);
v___x_1552_ = ((size_t)1ULL);
v___x_1553_ = lean_usize_sub(v___x_1551_, v___x_1552_);
v___x_1554_ = lean_usize_land(v___x_1550_, v___x_1553_);
v___x_1555_ = lean_array_uget_borrowed(v_buckets_1540_, v___x_1554_);
v___x_1556_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(v_a_1539_, v___x_1555_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___boxed(lean_object* v_m_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(v_m_1559_, v_a_1560_);
lean_dec(v_a_1560_);
lean_dec_ref(v_m_1559_);
return v_res_1561_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__1));
v___x_1565_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__0));
v___x_1566_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1565_, v___x_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(lean_object* v_declName_1569_, uint8_t v_isMeta_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v_env_1582_; lean_object* v___y_1584_; lean_object* v___x_1597_; 
v___x_1578_ = lean_st_ref_get(v___y_1576_);
v_env_1582_ = lean_ctor_get(v___x_1578_, 0);
lean_inc_ref(v_env_1582_);
lean_dec(v___x_1578_);
v___x_1597_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1582_, v_declName_1569_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_dec_ref(v_env_1582_);
lean_dec(v_declName_1569_);
goto v___jp_1579_;
}
else
{
lean_object* v_val_1598_; lean_object* v___x_1599_; lean_object* v_modules_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v_val_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_val_1598_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = l_Lean_Environment_header(v_env_1582_);
v_modules_1600_ = lean_ctor_get(v___x_1599_, 3);
lean_inc_ref(v_modules_1600_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = lean_array_get_size(v_modules_1600_);
v___x_1602_ = lean_nat_dec_lt(v_val_1598_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_dec_ref(v_modules_1600_);
lean_dec(v_val_1598_);
lean_dec_ref(v_env_1582_);
lean_dec(v_declName_1569_);
goto v___jp_1579_;
}
else
{
lean_object* v___x_1603_; lean_object* v_env_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___y_1608_; 
v___x_1603_ = lean_st_ref_get(v___y_1576_);
v_env_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc_ref(v_env_1604_);
lean_dec(v___x_1603_);
v___x_1605_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2);
v___x_1606_ = lean_array_fget(v_modules_1600_, v_val_1598_);
lean_dec(v_val_1598_);
lean_dec_ref(v_modules_1600_);
if (v_isMeta_1570_ == 0)
{
lean_dec_ref(v_env_1604_);
v___y_1608_ = v_isMeta_1570_;
goto v___jp_1607_;
}
else
{
uint8_t v___x_1619_; 
lean_inc(v_declName_1569_);
v___x_1619_ = l_Lean_isMarkedMeta(v_env_1604_, v_declName_1569_);
if (v___x_1619_ == 0)
{
v___y_1608_ = v_isMeta_1570_;
goto v___jp_1607_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = 0;
v___y_1608_ = v___x_1620_;
goto v___jp_1607_;
}
}
v___jp_1607_:
{
lean_object* v_toImport_1609_; lean_object* v_module_1610_; lean_object* v___x_1611_; 
v_toImport_1609_ = lean_ctor_get(v___x_1606_, 0);
lean_inc_ref(v_toImport_1609_);
lean_dec(v___x_1606_);
v_module_1610_ = lean_ctor_get(v_toImport_1609_, 0);
lean_inc(v_module_1610_);
lean_dec_ref(v_toImport_1609_);
lean_inc(v_declName_1569_);
v___x_1611_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(v_module_1610_, v___y_1608_, v_declName_1569_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec_ref(v___x_1611_);
v___x_1612_ = l_Lean_indirectModUseExt;
v___x_1613_ = lean_box(1);
v___x_1614_ = lean_box(0);
lean_inc_ref(v_env_1582_);
v___x_1615_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1605_, v___x_1612_, v_env_1582_, v___x_1613_, v___x_1614_);
v___x_1616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(v___x_1615_, v_declName_1569_);
lean_dec(v___x_1615_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1617_; 
v___x_1617_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__3));
v___y_1584_ = v___x_1617_;
goto v___jp_1583_;
}
else
{
lean_object* v_val_1618_; 
v_val_1618_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1618_);
lean_dec_ref(v___x_1616_);
v___y_1584_ = v_val_1618_;
goto v___jp_1583_;
}
}
else
{
lean_dec_ref(v_env_1582_);
lean_dec(v_declName_1569_);
return v___x_1611_;
}
}
}
}
v___jp_1579_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
v___jp_1583_:
{
lean_object* v___x_1585_; size_t v_sz_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v___x_1585_ = lean_box(0);
v_sz_1586_ = lean_array_size(v___y_1584_);
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(v_env_1582_, v_declName_1569_, v___y_1584_, v_sz_1586_, v___x_1587_, v___x_1585_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec_ref(v___y_1584_);
lean_dec_ref(v_env_1582_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v___x_1588_, 0);
lean_dec(v_unused_1596_);
v___x_1590_ = v___x_1588_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_dec(v___x_1588_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1585_);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1585_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
else
{
return v___x_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___boxed(lean_object* v_declName_1621_, lean_object* v_isMeta_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v_isMeta_boxed_1630_; lean_object* v_res_1631_; 
v_isMeta_boxed_1630_ = lean_unbox(v_isMeta_1622_);
v_res_1631_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v_declName_1621_, v_isMeta_boxed_1630_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(lean_object* v_as_x27_1632_, lean_object* v_b_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
if (lean_obj_tag(v_as_x27_1632_) == 0)
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v_b_1633_);
return v___x_1641_;
}
else
{
lean_object* v_head_1642_; lean_object* v_tail_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; 
v_head_1642_ = lean_ctor_get(v_as_x27_1632_, 0);
v_tail_1643_ = lean_ctor_get(v_as_x27_1632_, 1);
v___x_1644_ = 1;
lean_inc(v_head_1642_);
v___x_1645_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v_head_1642_, v___x_1644_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref(v___x_1645_);
v___x_1646_ = lean_box(0);
v_as_x27_1632_ = v_tail_1643_;
v_b_1633_ = v___x_1646_;
goto _start;
}
else
{
return v___x_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg___boxed(lean_object* v_as_x27_1648_, lean_object* v_b_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(v_as_x27_1648_, v_b_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v_as_x27_1648_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(lean_object* v_x_1658_, lean_object* v___y_1659_){
_start:
{
if (lean_obj_tag(v_x_1658_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1661_; 
v_a_1660_ = lean_ctor_get(v_x_1658_, 0);
lean_inc(v_a_1660_);
v___x_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1661_, 0, v_a_1660_);
lean_ctor_set(v___x_1661_, 1, v___y_1659_);
return v___x_1661_;
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v_x_1658_, 0);
lean_inc(v_a_1662_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v_a_1662_);
lean_ctor_set(v___x_1663_, 1, v___y_1659_);
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___boxed(lean_object* v_x_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_x_1664_, v___y_1665_);
lean_dec_ref(v_x_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(lean_object* v_env_1667_, lean_object* v_stx_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1667_, v_stx_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
if (lean_obj_tag(v_a_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
v_a_1673_ = lean_ctor_get(v___x_1671_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; 
v_unused_1682_ = lean_ctor_get(v___x_1671_, 0);
lean_dec(v_unused_1682_);
v___x_1675_ = v___x_1671_;
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1671_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_box(0);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_a_1673_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_object* v_val_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1711_; 
v_val_1683_ = lean_ctor_get(v_a_1672_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_a_1672_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1685_ = v_a_1672_;
v_isShared_1686_ = v_isSharedCheck_1711_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_val_1683_);
lean_dec(v_a_1672_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1711_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_snd_1687_; 
v_snd_1687_ = lean_ctor_get(v_val_1683_, 1);
lean_inc(v_snd_1687_);
lean_dec(v_val_1683_);
if (lean_obj_tag(v_snd_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1697_; 
lean_del_object(v___x_1685_);
v_a_1688_ = lean_ctor_get(v___x_1671_, 1);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1671_);
v_a_1689_ = lean_ctor_get(v_snd_1687_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_snd_1687_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1691_ = v_snd_1687_;
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v_snd_1687_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v___x_1694_, v_a_1688_);
lean_dec_ref(v___x_1694_);
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1710_; 
v_a_1698_ = lean_ctor_get(v___x_1671_, 1);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1671_);
v_a_1699_ = lean_ctor_get(v_snd_1687_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_snd_1687_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1701_ = v_snd_1687_;
v_isShared_1702_ = v_isSharedCheck_1710_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v_snd_1687_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1710_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v_a_1699_);
v___x_1704_ = v___x_1685_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1704_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v___x_1706_, v_a_1698_);
lean_dec_ref(v___x_1706_);
return v___x_1707_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_a_1712_ = lean_ctor_get(v___x_1671_, 0);
v_a_1713_ = lean_ctor_get(v___x_1671_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1671_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_inc(v_a_1712_);
lean_dec(v___x_1671_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1712_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed(lean_object* v_env_1721_, lean_object* v_stx_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(v_env_1721_, v_stx_1722_, v___y_1723_, v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(lean_object* v_env_1726_, lean_object* v_options_1727_, lean_object* v_currNamespace_1728_, lean_object* v_openDecls_1729_, lean_object* v_n_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = l_Lean_ResolveName_resolveGlobalName(v_env_1726_, v_options_1727_, v_currNamespace_1728_, v_openDecls_1729_, v_n_1730_);
v___x_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
lean_ctor_set(v___x_1734_, 1, v___y_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed(lean_object* v_env_1735_, lean_object* v_options_1736_, lean_object* v_currNamespace_1737_, lean_object* v_openDecls_1738_, lean_object* v_n_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(v_env_1735_, v_options_1736_, v_currNamespace_1737_, v_openDecls_1738_, v_n_1739_, v___y_1740_, v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v_options_1736_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(lean_object* v_currNamespace_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_currNamespace_1743_);
lean_ctor_set(v___x_1746_, 1, v___y_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed(lean_object* v_currNamespace_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(v_currNamespace_1747_, v___y_1748_, v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(lean_object* v_env_1751_, lean_object* v_declName_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v___x_1755_; lean_object* v_env_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; 
v___x_1755_ = 0;
v_env_1756_ = l_Lean_Environment_setExporting(v_env_1751_, v___x_1755_);
lean_inc(v_declName_1752_);
v___x_1757_ = l_Lean_mkPrivateName(v_env_1756_, v_declName_1752_);
v___x_1758_ = 1;
lean_inc_ref(v_env_1756_);
v___x_1759_ = l_Lean_Environment_contains(v_env_1756_, v___x_1757_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; uint8_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = l_Lean_privateToUserName(v_declName_1752_);
v___x_1761_ = l_Lean_Environment_contains(v_env_1756_, v___x_1760_, v___x_1758_);
v___x_1762_ = lean_box(v___x_1761_);
v___x_1763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___y_1754_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec_ref(v_env_1756_);
lean_dec(v_declName_1752_);
v___x_1764_ = lean_box(v___x_1759_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
lean_ctor_set(v___x_1765_, 1, v___y_1754_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed(lean_object* v_env_1766_, lean_object* v_declName_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(v_env_1766_, v_declName_1767_, v___y_1768_, v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1770_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = l_Lean_maxRecDepthErrorMessage;
v___x_1777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3);
v___x_1779_ = l_Lean_MessageData_ofFormat(v___x_1778_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4);
v___x_1781_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__2));
v___x_1782_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v___x_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(lean_object* v_ref_1783_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_ref_1783_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___boxed(lean_object* v_ref_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(v_ref_1788_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(lean_object* v_env_1791_, lean_object* v_currNamespace_1792_, lean_object* v_openDecls_1793_, lean_object* v_n_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = l_Lean_ResolveName_resolveNamespace(v_env_1791_, v_currNamespace_1792_, v_openDecls_1793_, v_n_1794_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v___y_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed(lean_object* v_env_1799_, lean_object* v_currNamespace_1800_, lean_object* v_openDecls_1801_, lean_object* v_n_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(v_env_1799_, v_currNamespace_1800_, v_openDecls_1801_, v_n_1802_, v___y_1803_, v___y_1804_);
lean_dec_ref(v___y_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(lean_object* v_as_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
if (lean_obj_tag(v_as_1806_) == 0)
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_box(0);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
else
{
lean_object* v_options_1816_; uint8_t v_hasTrace_1817_; 
v_options_1816_ = lean_ctor_get(v___y_1811_, 2);
v_hasTrace_1817_ = lean_ctor_get_uint8(v_options_1816_, sizeof(void*)*1);
if (v_hasTrace_1817_ == 0)
{
lean_object* v_tail_1818_; 
v_tail_1818_ = lean_ctor_get(v_as_1806_, 1);
lean_inc(v_tail_1818_);
lean_dec_ref(v_as_1806_);
v_as_1806_ = v_tail_1818_;
goto _start;
}
else
{
lean_object* v_head_1820_; lean_object* v_tail_1821_; lean_object* v_fst_1822_; lean_object* v_snd_1823_; lean_object* v_inheritedTraceOptions_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v_head_1820_ = lean_ctor_get(v_as_1806_, 0);
lean_inc(v_head_1820_);
v_tail_1821_ = lean_ctor_get(v_as_1806_, 1);
lean_inc(v_tail_1821_);
lean_dec_ref(v_as_1806_);
v_fst_1822_ = lean_ctor_get(v_head_1820_, 0);
lean_inc_n(v_fst_1822_, 2);
v_snd_1823_ = lean_ctor_get(v_head_1820_, 1);
lean_inc(v_snd_1823_);
lean_dec(v_head_1820_);
v_inheritedTraceOptions_1824_ = lean_ctor_get(v___y_1811_, 13);
v___x_1825_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__10));
v___x_1826_ = l_Lean_Name_append(v___x_1825_, v_fst_1822_);
v___x_1827_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1824_, v_options_1816_, v___x_1826_);
lean_dec(v___x_1826_);
if (v___x_1827_ == 0)
{
lean_dec(v_snd_1823_);
lean_dec(v_fst_1822_);
v_as_1806_ = v_tail_1821_;
goto _start;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_snd_1823_);
v___x_1830_ = l_Lean_MessageData_ofFormat(v___x_1829_);
v___x_1831_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_fst_1822_, v___x_1830_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec_ref(v___x_1831_);
v_as_1806_ = v_tail_1821_;
goto _start;
}
else
{
lean_dec(v_tail_1821_);
return v___x_1831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___boxed(lean_object* v_as_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(v_as_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(lean_object* v_x_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; lean_object* v_env_1852_; lean_object* v_options_1853_; lean_object* v_currRecDepth_1854_; lean_object* v_maxRecDepth_1855_; lean_object* v_ref_1856_; lean_object* v_currNamespace_1857_; lean_object* v_openDecls_1858_; lean_object* v_quotContext_1859_; lean_object* v_currMacroScope_1860_; lean_object* v___x_1861_; lean_object* v_nextMacroScope_1862_; lean_object* v___f_1863_; lean_object* v___f_1864_; lean_object* v___f_1865_; lean_object* v___f_1866_; lean_object* v___f_1867_; lean_object* v_methods_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1851_ = lean_st_ref_get(v___y_1849_);
v_env_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc_ref_n(v_env_1852_, 4);
lean_dec(v___x_1851_);
v_options_1853_ = lean_ctor_get(v___y_1848_, 2);
v_currRecDepth_1854_ = lean_ctor_get(v___y_1848_, 3);
v_maxRecDepth_1855_ = lean_ctor_get(v___y_1848_, 4);
v_ref_1856_ = lean_ctor_get(v___y_1848_, 5);
v_currNamespace_1857_ = lean_ctor_get(v___y_1848_, 6);
v_openDecls_1858_ = lean_ctor_get(v___y_1848_, 7);
v_quotContext_1859_ = lean_ctor_get(v___y_1848_, 10);
v_currMacroScope_1860_ = lean_ctor_get(v___y_1848_, 11);
v___x_1861_ = lean_st_ref_get(v___y_1849_);
v_nextMacroScope_1862_ = lean_ctor_get(v___x_1861_, 1);
lean_inc(v_nextMacroScope_1862_);
lean_dec(v___x_1861_);
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1863_, 0, v_env_1852_);
v___f_1864_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1864_, 0, v_env_1852_);
lean_inc_n(v_openDecls_1858_, 2);
lean_inc_n(v_currNamespace_1857_, 3);
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1865_, 0, v_env_1852_);
lean_closure_set(v___f_1865_, 1, v_currNamespace_1857_);
lean_closure_set(v___f_1865_, 2, v_openDecls_1858_);
v___f_1866_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1866_, 0, v_currNamespace_1857_);
lean_inc_ref(v_options_1853_);
v___f_1867_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1867_, 0, v_env_1852_);
lean_closure_set(v___f_1867_, 1, v_options_1853_);
lean_closure_set(v___f_1867_, 2, v_currNamespace_1857_);
lean_closure_set(v___f_1867_, 3, v_openDecls_1858_);
v_methods_1868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1868_, 0, v___f_1863_);
lean_ctor_set(v_methods_1868_, 1, v___f_1866_);
lean_ctor_set(v_methods_1868_, 2, v___f_1864_);
lean_ctor_set(v_methods_1868_, 3, v___f_1865_);
lean_ctor_set(v_methods_1868_, 4, v___f_1867_);
lean_inc(v_ref_1856_);
lean_inc(v_maxRecDepth_1855_);
lean_inc(v_currRecDepth_1854_);
lean_inc(v_currMacroScope_1860_);
lean_inc(v_quotContext_1859_);
v___x_1869_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1869_, 0, v_methods_1868_);
lean_ctor_set(v___x_1869_, 1, v_quotContext_1859_);
lean_ctor_set(v___x_1869_, 2, v_currMacroScope_1860_);
lean_ctor_set(v___x_1869_, 3, v_currRecDepth_1854_);
lean_ctor_set(v___x_1869_, 4, v_maxRecDepth_1855_);
lean_ctor_set(v___x_1869_, 5, v_ref_1856_);
v___x_1870_ = lean_box(0);
v___x_1871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1871_, 0, v_nextMacroScope_1862_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
lean_ctor_set(v___x_1871_, 2, v___x_1870_);
v___x_1872_ = lean_apply_2(v_x_1843_, v___x_1869_, v___x_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v_a_1874_; lean_object* v_macroScope_1875_; lean_object* v_traceMsgs_1876_; lean_object* v_expandedMacroDecls_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 1);
lean_inc(v_a_1873_);
v_a_1874_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___x_1872_);
v_macroScope_1875_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_macroScope_1875_);
v_traceMsgs_1876_ = lean_ctor_get(v_a_1873_, 1);
lean_inc(v_traceMsgs_1876_);
v_expandedMacroDecls_1877_ = lean_ctor_get(v_a_1873_, 2);
lean_inc(v_expandedMacroDecls_1877_);
lean_dec(v_a_1873_);
v___x_1878_ = lean_box(0);
v___x_1879_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(v_expandedMacroDecls_1877_, v___x_1878_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v_expandedMacroDecls_1877_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1880_; lean_object* v_env_1881_; lean_object* v_ngen_1882_; lean_object* v_auxDeclNGen_1883_; lean_object* v_traceState_1884_; lean_object* v_cache_1885_; lean_object* v_messages_1886_; lean_object* v_infoState_1887_; lean_object* v_snapshotTasks_1888_; lean_object* v_newDecls_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v___x_1879_);
v___x_1880_ = lean_st_ref_take(v___y_1849_);
v_env_1881_ = lean_ctor_get(v___x_1880_, 0);
v_ngen_1882_ = lean_ctor_get(v___x_1880_, 2);
v_auxDeclNGen_1883_ = lean_ctor_get(v___x_1880_, 3);
v_traceState_1884_ = lean_ctor_get(v___x_1880_, 4);
v_cache_1885_ = lean_ctor_get(v___x_1880_, 5);
v_messages_1886_ = lean_ctor_get(v___x_1880_, 6);
v_infoState_1887_ = lean_ctor_get(v___x_1880_, 7);
v_snapshotTasks_1888_ = lean_ctor_get(v___x_1880_, 8);
v_newDecls_1889_ = lean_ctor_get(v___x_1880_, 9);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v___x_1880_, 1);
lean_dec(v_unused_1916_);
v___x_1891_ = v___x_1880_;
v_isShared_1892_ = v_isSharedCheck_1915_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_newDecls_1889_);
lean_inc(v_snapshotTasks_1888_);
lean_inc(v_infoState_1887_);
lean_inc(v_messages_1886_);
lean_inc(v_cache_1885_);
lean_inc(v_traceState_1884_);
lean_inc(v_auxDeclNGen_1883_);
lean_inc(v_ngen_1882_);
lean_inc(v_env_1881_);
lean_dec(v___x_1880_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1915_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v_macroScope_1875_);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_env_1881_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_macroScope_1875_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_ngen_1882_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_auxDeclNGen_1883_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_traceState_1884_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v_cache_1885_);
lean_ctor_set(v_reuseFailAlloc_1914_, 6, v_messages_1886_);
lean_ctor_set(v_reuseFailAlloc_1914_, 7, v_infoState_1887_);
lean_ctor_set(v_reuseFailAlloc_1914_, 8, v_snapshotTasks_1888_);
lean_ctor_set(v_reuseFailAlloc_1914_, 9, v_newDecls_1889_);
v___x_1894_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_st_ref_set(v___y_1849_, v___x_1894_);
v___x_1896_ = l_List_reverse___redArg(v_traceMsgs_1876_);
v___x_1897_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(v___x_1896_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; 
v_unused_1905_ = lean_ctor_get(v___x_1897_, 0);
lean_dec(v_unused_1905_);
v___x_1899_ = v___x_1897_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_dec(v___x_1897_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_a_1874_);
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1874_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_a_1874_);
v_a_1906_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1897_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1897_);
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
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_traceMsgs_1876_);
lean_dec(v_macroScope_1875_);
lean_dec(v_a_1874_);
v_a_1917_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1879_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1879_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_1925_; 
v_a_1925_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1872_);
if (lean_obj_tag(v_a_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v_a_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v_a_1926_ = lean_ctor_get(v_a_1925_, 0);
lean_inc(v_a_1926_);
v_a_1927_ = lean_ctor_get(v_a_1925_, 1);
lean_inc_ref(v_a_1927_);
lean_dec_ref(v_a_1925_);
v___x_1928_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0));
v___x_1929_ = lean_string_dec_eq(v_a_1927_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1927_);
v___x_1931_ = l_Lean_MessageData_ofFormat(v___x_1930_);
v___x_1932_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_a_1926_, v___x_1931_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v_a_1926_);
return v___x_1932_;
}
else
{
lean_object* v___x_1933_; 
lean_dec_ref(v_a_1927_);
v___x_1933_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(v_a_1926_);
return v___x_1933_;
}
}
else
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
return v___x_1934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___boxed(lean_object* v_x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v_x_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1943_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__0));
v___x_1946_ = l_Lean_stringToMessageData(v___x_1945_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__2));
v___x_1949_ = l_Lean_stringToMessageData(v___x_1948_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__4));
v___x_1952_ = l_Lean_stringToMessageData(v___x_1951_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6));
v___x_1955_ = l_Lean_stringToMessageData(v___x_1954_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8));
v___x_1958_ = l_Lean_stringToMessageData(v___x_1957_);
return v___x_1958_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__10));
v___x_1961_ = l_Lean_stringToMessageData(v___x_1960_);
return v___x_1961_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__15));
v___x_1971_ = l_Lean_stringToMessageData(v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1(lean_object* v___x_1972_, lean_object* v_attrInstance_1973_, lean_object* v___f_1974_, lean_object* v___x_1975_, lean_object* v___x_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_1972_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v_attr_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = lean_unsigned_to_nat(1u);
v_attr_1987_ = l_Lean_Syntax_getArg(v_attrInstance_1973_, v___x_1986_);
v___x_1988_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_1988_, 0, v_attr_1987_);
lean_closure_set(v___x_1988_, 1, v___f_1974_);
v___x_1989_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_1988_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2104_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2104_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2104_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___y_1995_; lean_object* v___y_2002_; lean_object* v___y_2003_; uint8_t v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v_attrName_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
lean_inc(v_a_1990_);
v___x_2085_ = l_Lean_Syntax_getKind(v_a_1990_);
v___x_2086_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__14));
v___x_2087_ = lean_name_eq(v___x_2085_, v___x_2086_);
if (v___x_2087_ == 0)
{
if (lean_obj_tag(v___x_2085_) == 1)
{
lean_object* v_str_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_str_2088_ = lean_ctor_get(v___x_2085_, 1);
lean_inc_ref(v_str_2088_);
lean_dec_ref(v___x_2085_);
v___x_2089_ = lean_box(0);
v___x_2090_ = l_Lean_Name_str___override(v___x_2089_, v_str_2088_);
v_attrName_2021_ = v___x_2090_;
v___y_2022_ = v___y_1977_;
v___y_2023_ = v___y_1978_;
v___y_2024_ = v___y_1979_;
v___y_2025_ = v___y_1980_;
v___y_2026_ = v___y_1981_;
v___y_2027_ = v___y_1982_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v___x_2085_);
lean_del_object(v___x_1992_);
lean_dec(v_a_1985_);
lean_dec(v___x_1975_);
v___x_2091_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__16);
v___x_2092_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_a_1990_, v___x_2091_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v_a_1990_);
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
lean_dec(v___x_2085_);
v___x_2101_ = l_Lean_Syntax_getArg(v_a_1990_, v___x_1976_);
v___x_2102_ = l_Lean_Syntax_getId(v___x_2101_);
lean_dec(v___x_2101_);
v___x_2103_ = lean_erase_macro_scopes(v___x_2102_);
v_attrName_2021_ = v___x_2103_;
v___y_2022_ = v___y_1977_;
v___y_2023_ = v___y_1978_;
v___y_2024_ = v___y_1979_;
v___y_2025_ = v___y_1980_;
v___y_2026_ = v___y_1981_;
v___y_2027_ = v___y_1982_;
goto v___jp_2020_;
}
v___jp_1994_:
{
lean_object* v___x_1996_; uint8_t v___x_1997_; lean_object* v___x_1999_; 
v___x_1996_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1996_, 0, v___y_1995_);
lean_ctor_set(v___x_1996_, 1, v_a_1990_);
v___x_1997_ = lean_unbox(v_a_1985_);
lean_dec(v_a_1985_);
lean_ctor_set_uint8(v___x_1996_, sizeof(void*)*2, v___x_1997_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1996_);
v___x_1999_ = v___x_1992_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1996_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
v___jp_2001_:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v___y_2002_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref(v___x_2011_);
v___y_1995_ = v___y_2003_;
goto v___jp_1994_;
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v___y_2003_);
lean_del_object(v___x_1992_);
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
v___jp_2020_:
{
lean_object* v___x_2028_; lean_object* v_env_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_st_ref_get(v___y_2027_);
v_env_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_ref(v_env_2029_);
lean_dec(v___x_2028_);
lean_inc(v_attrName_2021_);
v___x_2030_ = l_Lean_getAttributeImpl(v_env_2029_, v_attrName_2021_);
if (lean_obj_tag(v___x_2030_) == 1)
{
lean_object* v___x_2031_; lean_object* v_env_2032_; lean_object* v___x_2033_; 
lean_dec_ref(v___x_2030_);
v___x_2031_ = lean_st_ref_get(v___y_2027_);
v_env_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc_ref(v_env_2032_);
lean_dec(v___x_2031_);
lean_inc(v_attrName_2021_);
v___x_2033_ = l_Lean_getAttributeImpl(v_env_2032_, v_attrName_2021_);
if (lean_obj_tag(v___x_2033_) == 1)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; lean_object* v_toAttributeImplCore_2036_; lean_object* v_env_2037_; lean_object* v_ref_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = lean_st_ref_get(v___y_2027_);
v_toAttributeImplCore_2036_ = lean_ctor_get(v_a_2034_, 0);
lean_inc_ref(v_toAttributeImplCore_2036_);
lean_dec(v_a_2034_);
v_env_2037_ = lean_ctor_get(v___x_2035_, 0);
lean_inc_ref(v_env_2037_);
lean_dec(v___x_2035_);
v_ref_2038_ = lean_ctor_get(v_toAttributeImplCore_2036_, 0);
lean_inc_n(v_ref_2038_, 2);
lean_dec_ref(v_toAttributeImplCore_2036_);
v___x_2039_ = l_Lean_regularInitAttr;
v___x_2040_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1975_, v___x_2039_, v_env_2037_, v_ref_2038_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_dec(v_ref_2038_);
v___y_1995_ = v_attrName_2021_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2041_; lean_object* v_env_2042_; uint8_t v___x_2043_; lean_object* v___x_2044_; 
lean_dec_ref(v___x_2040_);
v___x_2041_ = lean_st_ref_get(v___y_2027_);
v_env_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_ref(v_env_2042_);
lean_dec(v___x_2041_);
v___x_2043_ = 1;
v___x_2044_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2042_, v_ref_2038_);
lean_dec_ref(v_env_2042_);
if (lean_obj_tag(v___x_2044_) == 1)
{
lean_object* v_val_2045_; lean_object* v___x_2046_; lean_object* v_env_2047_; lean_object* v___x_2048_; lean_object* v_modules_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v_val_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_val_2045_);
lean_dec_ref(v___x_2044_);
v___x_2046_ = lean_st_ref_get(v___y_2027_);
v_env_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_ref(v_env_2047_);
lean_dec(v___x_2046_);
v___x_2048_ = l_Lean_Environment_header(v_env_2047_);
lean_dec_ref(v_env_2047_);
v_modules_2049_ = lean_ctor_get(v___x_2048_, 3);
lean_inc_ref(v_modules_2049_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = lean_array_get_size(v_modules_2049_);
v___x_2051_ = lean_nat_dec_lt(v_val_2045_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_dec_ref(v_modules_2049_);
lean_dec(v_val_2045_);
v___y_2002_ = v_ref_2038_;
v___y_2003_ = v_attrName_2021_;
v___y_2004_ = v___x_2043_;
v___y_2005_ = v___y_2022_;
v___y_2006_ = v___y_2023_;
v___y_2007_ = v___y_2024_;
v___y_2008_ = v___y_2025_;
v___y_2009_ = v___y_2026_;
v___y_2010_ = v___y_2027_;
goto v___jp_2001_;
}
else
{
lean_object* v___x_2052_; uint8_t v_hasData_2053_; 
v___x_2052_ = lean_array_fget_borrowed(v_modules_2049_, v_val_2045_);
v_hasData_2053_ = lean_ctor_get_uint8(v___x_2052_, sizeof(void*)*1 + 1);
if (v_hasData_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v_toImport_2056_; lean_object* v_module_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_ref_2038_);
lean_del_object(v___x_1992_);
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
v___x_2054_ = l_Lean_instInhabitedEffectiveImport_default;
v___x_2055_ = lean_array_get(v___x_2054_, v_modules_2049_, v_val_2045_);
lean_dec(v_val_2045_);
lean_dec_ref(v_modules_2049_);
v_toImport_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc_ref(v_toImport_2056_);
lean_dec(v___x_2055_);
v_module_2057_ = lean_ctor_get(v_toImport_2056_, 0);
lean_inc(v_module_2057_);
lean_dec_ref(v_toImport_2056_);
v___x_2058_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1);
v___x_2059_ = l_Lean_MessageData_ofName(v_attrName_2021_);
v___x_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2058_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3);
v___x_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2060_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v___x_2063_ = l_Lean_MessageData_ofName(v_module_2057_);
lean_inc_ref(v___x_2063_);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___x_2063_);
v___x_2068_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2069_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
lean_dec_ref(v_modules_2049_);
lean_dec(v_val_2045_);
v___y_2002_ = v_ref_2038_;
v___y_2003_ = v_attrName_2021_;
v___y_2004_ = v___x_2043_;
v___y_2005_ = v___y_2022_;
v___y_2006_ = v___y_2023_;
v___y_2007_ = v___y_2024_;
v___y_2008_ = v___y_2025_;
v___y_2009_ = v___y_2026_;
v___y_2010_ = v___y_2027_;
goto v___jp_2001_;
}
}
}
else
{
lean_dec(v___x_2044_);
v___y_2002_ = v_ref_2038_;
v___y_2003_ = v_attrName_2021_;
v___y_2004_ = v___x_2043_;
v___y_2005_ = v___y_2022_;
v___y_2006_ = v___y_2023_;
v___y_2007_ = v___y_2024_;
v___y_2008_ = v___y_2025_;
v___y_2009_ = v___y_2026_;
v___y_2010_ = v___y_2027_;
goto v___jp_2001_;
}
}
}
else
{
lean_dec_ref(v___x_2033_);
lean_dec(v___x_1975_);
v___y_1995_ = v_attrName_2021_;
goto v___jp_1994_;
}
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec_ref(v___x_2030_);
lean_del_object(v___x_1992_);
lean_dec(v_a_1990_);
lean_dec(v_a_1985_);
lean_dec(v___x_1975_);
v___x_2079_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__9);
v___x_2080_ = l_Lean_MessageData_ofName(v_attrName_2021_);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__11);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2083_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
return v___x_2084_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_a_1985_);
lean_dec(v___x_1975_);
v_a_2105_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_1989_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_1989_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v___x_1975_);
lean_dec_ref(v___f_1974_);
v_a_2113_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_1984_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_1984_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___boxed(lean_object* v___x_2121_, lean_object* v_attrInstance_2122_, lean_object* v___f_2123_, lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1(v___x_2121_, v_attrInstance_2122_, v___f_2123_, v___x_2124_, v___x_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___x_2125_);
lean_dec(v_attrInstance_2122_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(lean_object* v___y_2134_, uint8_t v_isExporting_2135_, lean_object* v___x_2136_, lean_object* v___y_2137_, lean_object* v___x_2138_, lean_object* v_a_x3f_2139_){
_start:
{
lean_object* v___x_2141_; lean_object* v_env_2142_; lean_object* v_nextMacroScope_2143_; lean_object* v_ngen_2144_; lean_object* v_auxDeclNGen_2145_; lean_object* v_traceState_2146_; lean_object* v_messages_2147_; lean_object* v_infoState_2148_; lean_object* v_snapshotTasks_2149_; lean_object* v_newDecls_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2175_; 
v___x_2141_ = lean_st_ref_take(v___y_2134_);
v_env_2142_ = lean_ctor_get(v___x_2141_, 0);
v_nextMacroScope_2143_ = lean_ctor_get(v___x_2141_, 1);
v_ngen_2144_ = lean_ctor_get(v___x_2141_, 2);
v_auxDeclNGen_2145_ = lean_ctor_get(v___x_2141_, 3);
v_traceState_2146_ = lean_ctor_get(v___x_2141_, 4);
v_messages_2147_ = lean_ctor_get(v___x_2141_, 6);
v_infoState_2148_ = lean_ctor_get(v___x_2141_, 7);
v_snapshotTasks_2149_ = lean_ctor_get(v___x_2141_, 8);
v_newDecls_2150_ = lean_ctor_get(v___x_2141_, 9);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; 
v_unused_2176_ = lean_ctor_get(v___x_2141_, 5);
lean_dec(v_unused_2176_);
v___x_2152_ = v___x_2141_;
v_isShared_2153_ = v_isSharedCheck_2175_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_newDecls_2150_);
lean_inc(v_snapshotTasks_2149_);
lean_inc(v_infoState_2148_);
lean_inc(v_messages_2147_);
lean_inc(v_traceState_2146_);
lean_inc(v_auxDeclNGen_2145_);
lean_inc(v_ngen_2144_);
lean_inc(v_nextMacroScope_2143_);
lean_inc(v_env_2142_);
lean_dec(v___x_2141_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2175_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = l_Lean_Environment_setExporting(v_env_2142_, v_isExporting_2135_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 5, v___x_2136_);
lean_ctor_set(v___x_2152_, 0, v___x_2154_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_nextMacroScope_2143_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_ngen_2144_);
lean_ctor_set(v_reuseFailAlloc_2174_, 3, v_auxDeclNGen_2145_);
lean_ctor_set(v_reuseFailAlloc_2174_, 4, v_traceState_2146_);
lean_ctor_set(v_reuseFailAlloc_2174_, 5, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2174_, 6, v_messages_2147_);
lean_ctor_set(v_reuseFailAlloc_2174_, 7, v_infoState_2148_);
lean_ctor_set(v_reuseFailAlloc_2174_, 8, v_snapshotTasks_2149_);
lean_ctor_set(v_reuseFailAlloc_2174_, 9, v_newDecls_2150_);
v___x_2156_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v_mctx_2159_; lean_object* v_zetaDeltaFVarIds_2160_; lean_object* v_postponed_2161_; lean_object* v_diag_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2172_; 
v___x_2157_ = lean_st_ref_set(v___y_2134_, v___x_2156_);
v___x_2158_ = lean_st_ref_take(v___y_2137_);
v_mctx_2159_ = lean_ctor_get(v___x_2158_, 0);
v_zetaDeltaFVarIds_2160_ = lean_ctor_get(v___x_2158_, 2);
v_postponed_2161_ = lean_ctor_get(v___x_2158_, 3);
v_diag_2162_ = lean_ctor_get(v___x_2158_, 4);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; 
v_unused_2173_ = lean_ctor_get(v___x_2158_, 1);
lean_dec(v_unused_2173_);
v___x_2164_ = v___x_2158_;
v_isShared_2165_ = v_isSharedCheck_2172_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_diag_2162_);
lean_inc(v_postponed_2161_);
lean_inc(v_zetaDeltaFVarIds_2160_);
lean_inc(v_mctx_2159_);
lean_dec(v___x_2158_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2172_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v___x_2138_);
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_mctx_2159_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_zetaDeltaFVarIds_2160_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_postponed_2161_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v_diag_2162_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_st_ref_set(v___y_2137_, v___x_2167_);
v___x_2169_ = lean_box(0);
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
return v___x_2170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0___boxed(lean_object* v___y_2177_, lean_object* v_isExporting_2178_, lean_object* v___x_2179_, lean_object* v___y_2180_, lean_object* v___x_2181_, lean_object* v_a_x3f_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v_isExporting_boxed_2184_; lean_object* v_res_2185_; 
v_isExporting_boxed_2184_ = lean_unbox(v_isExporting_2178_);
v_res_2185_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(v___y_2177_, v_isExporting_boxed_2184_, v___x_2179_, v___y_2180_, v___x_2181_, v_a_x3f_2182_);
lean_dec(v_a_x3f_2182_);
lean_dec(v___y_2180_);
lean_dec(v___y_2177_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(lean_object* v_x_2186_, uint8_t v_isExporting_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; lean_object* v_env_2196_; uint8_t v_isExporting_2197_; lean_object* v___x_2198_; lean_object* v_env_2199_; lean_object* v_nextMacroScope_2200_; lean_object* v_ngen_2201_; lean_object* v_auxDeclNGen_2202_; lean_object* v_traceState_2203_; lean_object* v_messages_2204_; lean_object* v_infoState_2205_; lean_object* v_snapshotTasks_2206_; lean_object* v_newDecls_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2261_; 
v___x_2195_ = lean_st_ref_get(v___y_2193_);
v_env_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc_ref(v_env_2196_);
lean_dec(v___x_2195_);
v_isExporting_2197_ = lean_ctor_get_uint8(v_env_2196_, sizeof(void*)*8);
lean_dec_ref(v_env_2196_);
v___x_2198_ = lean_st_ref_take(v___y_2193_);
v_env_2199_ = lean_ctor_get(v___x_2198_, 0);
v_nextMacroScope_2200_ = lean_ctor_get(v___x_2198_, 1);
v_ngen_2201_ = lean_ctor_get(v___x_2198_, 2);
v_auxDeclNGen_2202_ = lean_ctor_get(v___x_2198_, 3);
v_traceState_2203_ = lean_ctor_get(v___x_2198_, 4);
v_messages_2204_ = lean_ctor_get(v___x_2198_, 6);
v_infoState_2205_ = lean_ctor_get(v___x_2198_, 7);
v_snapshotTasks_2206_ = lean_ctor_get(v___x_2198_, 8);
v_newDecls_2207_ = lean_ctor_get(v___x_2198_, 9);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2261_ == 0)
{
lean_object* v_unused_2262_; 
v_unused_2262_ = lean_ctor_get(v___x_2198_, 5);
lean_dec(v_unused_2262_);
v___x_2209_ = v___x_2198_;
v_isShared_2210_ = v_isSharedCheck_2261_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_newDecls_2207_);
lean_inc(v_snapshotTasks_2206_);
lean_inc(v_infoState_2205_);
lean_inc(v_messages_2204_);
lean_inc(v_traceState_2203_);
lean_inc(v_auxDeclNGen_2202_);
lean_inc(v_ngen_2201_);
lean_inc(v_nextMacroScope_2200_);
lean_inc(v_env_2199_);
lean_dec(v___x_2198_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2261_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2211_ = l_Lean_Environment_setExporting(v_env_2199_, v_isExporting_2187_);
v___x_2212_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 5, v___x_2212_);
lean_ctor_set(v___x_2209_, 0, v___x_2211_);
v___x_2214_ = v___x_2209_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_nextMacroScope_2200_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_ngen_2201_);
lean_ctor_set(v_reuseFailAlloc_2260_, 3, v_auxDeclNGen_2202_);
lean_ctor_set(v_reuseFailAlloc_2260_, 4, v_traceState_2203_);
lean_ctor_set(v_reuseFailAlloc_2260_, 5, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2260_, 6, v_messages_2204_);
lean_ctor_set(v_reuseFailAlloc_2260_, 7, v_infoState_2205_);
lean_ctor_set(v_reuseFailAlloc_2260_, 8, v_snapshotTasks_2206_);
lean_ctor_set(v_reuseFailAlloc_2260_, 9, v_newDecls_2207_);
v___x_2214_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v_mctx_2217_; lean_object* v_zetaDeltaFVarIds_2218_; lean_object* v_postponed_2219_; lean_object* v_diag_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2258_; 
v___x_2215_ = lean_st_ref_set(v___y_2193_, v___x_2214_);
v___x_2216_ = lean_st_ref_take(v___y_2191_);
v_mctx_2217_ = lean_ctor_get(v___x_2216_, 0);
v_zetaDeltaFVarIds_2218_ = lean_ctor_get(v___x_2216_, 2);
v_postponed_2219_ = lean_ctor_get(v___x_2216_, 3);
v_diag_2220_ = lean_ctor_get(v___x_2216_, 4);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; 
v_unused_2259_ = lean_ctor_get(v___x_2216_, 1);
lean_dec(v_unused_2259_);
v___x_2222_ = v___x_2216_;
v_isShared_2223_ = v_isSharedCheck_2258_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_diag_2220_);
lean_inc(v_postponed_2219_);
lean_inc(v_zetaDeltaFVarIds_2218_);
lean_inc(v_mctx_2217_);
lean_dec(v___x_2216_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2258_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_mctx_2217_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_zetaDeltaFVarIds_2218_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_postponed_2219_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v_diag_2220_);
v___x_2226_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v_r_2228_; 
v___x_2227_ = lean_st_ref_set(v___y_2191_, v___x_2226_);
lean_inc(v___y_2193_);
lean_inc_ref(v___y_2192_);
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
lean_inc_ref(v___y_2188_);
v_r_2228_ = lean_apply_7(v_x_2186_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, lean_box(0));
if (lean_obj_tag(v_r_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2245_; 
v_a_2229_ = lean_ctor_get(v_r_2228_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_r_2228_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2231_ = v_r_2228_;
v_isShared_2232_ = v_isSharedCheck_2245_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v_r_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2245_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
lean_inc(v_a_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 1);
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v___x_2235_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(v___y_2193_, v_isExporting_2197_, v___x_2212_, v___y_2191_, v___x_2224_, v___x_2234_);
lean_dec_ref(v___x_2234_);
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
lean_ctor_set(v___x_2237_, 0, v_a_2229_);
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2229_);
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
else
{
lean_object* v_a_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
v_a_2246_ = lean_ctor_get(v_r_2228_, 0);
lean_inc(v_a_2246_);
lean_dec_ref(v_r_2228_);
v___x_2247_ = lean_box(0);
v___x_2248_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(v___y_2193_, v_isExporting_2197_, v___x_2212_, v___y_2191_, v___x_2224_, v___x_2247_);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v___x_2248_, 0);
lean_dec(v_unused_2256_);
v___x_2250_ = v___x_2248_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_dec(v___x_2248_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set_tag(v___x_2250_, 1);
lean_ctor_set(v___x_2250_, 0, v_a_2246_);
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2246_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___boxed(lean_object* v_x_2263_, lean_object* v_isExporting_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
uint8_t v_isExporting_boxed_2272_; lean_object* v_res_2273_; 
v_isExporting_boxed_2272_ = lean_unbox(v_isExporting_2264_);
v_res_2273_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(v_x_2263_, v_isExporting_boxed_2272_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(lean_object* v_x_2274_, uint8_t v_when_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
if (v_when_2275_ == 0)
{
lean_object* v___x_2283_; 
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
v___x_2283_ = lean_apply_7(v_x_2274_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, lean_box(0));
return v___x_2283_;
}
else
{
uint8_t v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = 0;
v___x_2285_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(v_x_2274_, v___x_2284_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg___boxed(lean_object* v_x_2286_, lean_object* v_when_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
uint8_t v_when_boxed_2295_; lean_object* v_res_2296_; 
v_when_boxed_2295_ = lean_unbox(v_when_2287_);
v_res_2296_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(v_x_2286_, v_when_boxed_2295_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(lean_object* v_attrInstance_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___f_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___f_2311_; uint8_t v___x_2312_; lean_object* v___x_2313_; 
v___f_2306_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___closed__0));
v___x_2307_ = lean_box(0);
v___x_2308_ = lean_unsigned_to_nat(0u);
v___x_2309_ = l_Lean_Syntax_getArg(v_attrInstance_2298_, v___x_2308_);
v___x_2310_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2310_, 0, v___x_2309_);
v___f_2311_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___boxed), 12, 5);
lean_closure_set(v___f_2311_, 0, v___x_2310_);
lean_closure_set(v___f_2311_, 1, v_attrInstance_2298_);
lean_closure_set(v___f_2311_, 2, v___f_2306_);
lean_closure_set(v___f_2311_, 3, v___x_2307_);
lean_closure_set(v___f_2311_, 4, v___x_2308_);
v___x_2312_ = 1;
v___x_2313_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(v___f_2311_, v___x_2312_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___boxed(lean_object* v_attrInstance_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(v_attrInstance_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(lean_object* v_as_2323_, size_t v_sz_2324_, size_t v_i_2325_, lean_object* v_b_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_snd_2335_; uint8_t v___x_2339_; 
v___x_2339_ = lean_usize_dec_lt(v_i_2325_, v_sz_2324_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v_b_2326_);
return v___x_2340_;
}
else
{
lean_object* v_fileName_2341_; lean_object* v_fileMap_2342_; lean_object* v_options_2343_; lean_object* v_currRecDepth_2344_; lean_object* v_maxRecDepth_2345_; lean_object* v_ref_2346_; lean_object* v_currNamespace_2347_; lean_object* v_openDecls_2348_; lean_object* v_initHeartbeats_2349_; lean_object* v_maxHeartbeats_2350_; lean_object* v_quotContext_2351_; lean_object* v_currMacroScope_2352_; uint8_t v_diag_2353_; lean_object* v_cancelTk_x3f_2354_; uint8_t v_suppressElabErrors_2355_; lean_object* v_inheritedTraceOptions_2356_; lean_object* v_a_2357_; lean_object* v_ref_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_fileName_2341_ = lean_ctor_get(v___y_2331_, 0);
v_fileMap_2342_ = lean_ctor_get(v___y_2331_, 1);
v_options_2343_ = lean_ctor_get(v___y_2331_, 2);
v_currRecDepth_2344_ = lean_ctor_get(v___y_2331_, 3);
v_maxRecDepth_2345_ = lean_ctor_get(v___y_2331_, 4);
v_ref_2346_ = lean_ctor_get(v___y_2331_, 5);
v_currNamespace_2347_ = lean_ctor_get(v___y_2331_, 6);
v_openDecls_2348_ = lean_ctor_get(v___y_2331_, 7);
v_initHeartbeats_2349_ = lean_ctor_get(v___y_2331_, 8);
v_maxHeartbeats_2350_ = lean_ctor_get(v___y_2331_, 9);
v_quotContext_2351_ = lean_ctor_get(v___y_2331_, 10);
v_currMacroScope_2352_ = lean_ctor_get(v___y_2331_, 11);
v_diag_2353_ = lean_ctor_get_uint8(v___y_2331_, sizeof(void*)*14);
v_cancelTk_x3f_2354_ = lean_ctor_get(v___y_2331_, 12);
v_suppressElabErrors_2355_ = lean_ctor_get_uint8(v___y_2331_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2356_ = lean_ctor_get(v___y_2331_, 13);
v_a_2357_ = lean_array_uget_borrowed(v_as_2323_, v_i_2325_);
v_ref_2358_ = l_Lean_replaceRef(v_a_2357_, v_ref_2346_);
lean_inc_ref(v_inheritedTraceOptions_2356_);
lean_inc(v_cancelTk_x3f_2354_);
lean_inc(v_currMacroScope_2352_);
lean_inc(v_quotContext_2351_);
lean_inc(v_maxHeartbeats_2350_);
lean_inc(v_initHeartbeats_2349_);
lean_inc(v_openDecls_2348_);
lean_inc(v_currNamespace_2347_);
lean_inc(v_maxRecDepth_2345_);
lean_inc(v_currRecDepth_2344_);
lean_inc_ref(v_options_2343_);
lean_inc_ref(v_fileMap_2342_);
lean_inc_ref(v_fileName_2341_);
v___x_2359_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2359_, 0, v_fileName_2341_);
lean_ctor_set(v___x_2359_, 1, v_fileMap_2342_);
lean_ctor_set(v___x_2359_, 2, v_options_2343_);
lean_ctor_set(v___x_2359_, 3, v_currRecDepth_2344_);
lean_ctor_set(v___x_2359_, 4, v_maxRecDepth_2345_);
lean_ctor_set(v___x_2359_, 5, v_ref_2358_);
lean_ctor_set(v___x_2359_, 6, v_currNamespace_2347_);
lean_ctor_set(v___x_2359_, 7, v_openDecls_2348_);
lean_ctor_set(v___x_2359_, 8, v_initHeartbeats_2349_);
lean_ctor_set(v___x_2359_, 9, v_maxHeartbeats_2350_);
lean_ctor_set(v___x_2359_, 10, v_quotContext_2351_);
lean_ctor_set(v___x_2359_, 11, v_currMacroScope_2352_);
lean_ctor_set(v___x_2359_, 12, v_cancelTk_x3f_2354_);
lean_ctor_set(v___x_2359_, 13, v_inheritedTraceOptions_2356_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*14, v_diag_2353_);
lean_ctor_set_uint8(v___x_2359_, sizeof(void*)*14 + 1, v_suppressElabErrors_2355_);
lean_inc(v_a_2357_);
v___x_2360_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(v_a_2357_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___x_2359_, v___y_2332_);
lean_dec_ref(v___x_2359_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2362_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref(v___x_2360_);
v___x_2362_ = lean_array_push(v_b_2326_, v_a_2361_);
v_snd_2335_ = v___x_2362_;
goto v___jp_2334_;
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2383_; 
v_a_2363_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2365_ = v___x_2360_;
v_isShared_2366_ = v_isSharedCheck_2383_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2360_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2383_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
uint8_t v___y_2368_; uint8_t v___x_2381_; 
v___x_2381_ = l_Lean_Exception_isInterrupt(v_a_2363_);
if (v___x_2381_ == 0)
{
uint8_t v___x_2382_; 
lean_inc(v_a_2363_);
v___x_2382_ = l_Lean_Exception_isRuntime(v_a_2363_);
v___y_2368_ = v___x_2382_;
goto v___jp_2367_;
}
else
{
v___y_2368_ = v___x_2381_;
goto v___jp_2367_;
}
v___jp_2367_:
{
if (v___y_2368_ == 0)
{
lean_object* v___x_2369_; 
lean_del_object(v___x_2365_);
v___x_2369_ = l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32(v_a_2363_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_dec_ref(v___x_2369_);
v_snd_2335_ = v_b_2326_;
goto v___jp_2334_;
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec_ref(v_b_2326_);
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v___x_2379_; 
lean_dec_ref(v_b_2326_);
if (v_isShared_2366_ == 0)
{
v___x_2379_ = v___x_2365_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2363_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
}
v___jp_2334_:
{
size_t v___x_2336_; size_t v___x_2337_; 
v___x_2336_ = ((size_t)1ULL);
v___x_2337_ = lean_usize_add(v_i_2325_, v___x_2336_);
v_i_2325_ = v___x_2337_;
v_b_2326_ = v_snd_2335_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33___boxed(lean_object* v_as_2384_, lean_object* v_sz_2385_, lean_object* v_i_2386_, lean_object* v_b_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
size_t v_sz_boxed_2395_; size_t v_i_boxed_2396_; lean_object* v_res_2397_; 
v_sz_boxed_2395_ = lean_unbox_usize(v_sz_2385_);
lean_dec(v_sz_2385_);
v_i_boxed_2396_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(v_as_2384_, v_sz_boxed_2395_, v_i_boxed_2396_, v_b_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec_ref(v_as_2384_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(lean_object* v_attrInstances_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v_attrs_2408_; size_t v_sz_2409_; size_t v___x_2410_; lean_object* v___x_2411_; 
v_attrs_2408_ = ((lean_object*)(l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___closed__0));
v_sz_2409_ = lean_array_size(v_attrInstances_2400_);
v___x_2410_ = ((size_t)0ULL);
v___x_2411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(v_attrInstances_2400_, v_sz_2409_, v___x_2410_, v_attrs_2408_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___boxed(lean_object* v_attrInstances_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(v_attrInstances_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec_ref(v_attrInstances_2412_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(lean_object* v_stx_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2429_ = lean_unsigned_to_nat(1u);
v___x_2430_ = l_Lean_Syntax_getArg(v_stx_2421_, v___x_2429_);
v___x_2431_ = l_Lean_Syntax_getSepArgs(v___x_2430_);
lean_dec(v___x_2430_);
v___x_2432_ = l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(v___x_2431_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec_ref(v___x_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9___boxed(lean_object* v_stx_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(v_stx_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v_stx_2433_);
return v_res_2441_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__0));
v___x_2444_ = l_Lean_stringToMessageData(v___x_2443_);
return v___x_2444_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__2));
v___x_2447_ = l_Lean_stringToMessageData(v___x_2446_);
return v___x_2447_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__4));
v___x_2450_ = l_Lean_stringToMessageData(v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5(lean_object* v_addInfo_2451_, lean_object* v_declName_2452_, uint8_t v___x_2453_, lean_object* v___f_2454_, uint8_t v___x_2455_, lean_object* v_env_2456_, lean_object* v___f_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2465_; 
lean_inc(v___y_2463_);
lean_inc_ref(v___y_2462_);
lean_inc(v___y_2461_);
lean_inc_ref(v___y_2460_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v_declName_2452_);
v___x_2465_ = lean_apply_8(v_addInfo_2451_, v_declName_2452_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, lean_box(0));
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v___x_2466_; 
lean_dec_ref(v___x_2465_);
lean_inc(v_declName_2452_);
v___x_2466_ = lean_private_to_user_name(v_declName_2452_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2467_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2468_ = l_Lean_MessageData_ofConstName(v_declName_2452_, v___x_2453_);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2471_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v___x_2472_;
}
else
{
lean_object* v_val_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_dec(v_declName_2452_);
v_val_2473_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_val_2473_);
lean_dec_ref(v___x_2466_);
v___x_2474_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5);
v___x_2475_ = l_Lean_MessageData_ofConstName(v_val_2473_, v___x_2453_);
v___x_2476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2474_);
lean_ctor_set(v___x_2476_, 1, v___x_2475_);
v___x_2477_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2478_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v___x_2479_;
}
}
else
{
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v_declName_2452_);
return v___x_2465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___boxed(lean_object* v_addInfo_2480_, lean_object* v_declName_2481_, lean_object* v___x_2482_, lean_object* v___f_2483_, lean_object* v___x_2484_, lean_object* v_env_2485_, lean_object* v___f_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
uint8_t v___x_56187__boxed_2494_; uint8_t v___x_56189__boxed_2495_; lean_object* v_res_2496_; 
v___x_56187__boxed_2494_ = lean_unbox(v___x_2482_);
v___x_56189__boxed_2495_ = lean_unbox(v___x_2484_);
v_res_2496_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5(v_addInfo_2480_, v_declName_2481_, v___x_56187__boxed_2494_, v___f_2483_, v___x_56189__boxed_2495_, v_env_2485_, v___f_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec_ref(v___f_2486_);
lean_dec_ref(v_env_2485_);
lean_dec_ref(v___f_2483_);
return v_res_2496_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__0));
v___x_2499_ = l_Lean_stringToMessageData(v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3(lean_object* v___f_2500_, lean_object* v_declName_2501_, uint8_t v___x_2502_, lean_object* v_env_2503_, lean_object* v_____do__lift_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
uint8_t v___y_2513_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
lean_inc(v_declName_2501_);
v___x_2522_ = l_Lean_privateToUserName(v_declName_2501_);
lean_inc_ref(v_env_2503_);
v___x_2523_ = lean_is_reserved_name(v_env_2503_, v___x_2522_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; uint8_t v___x_2525_; 
lean_inc(v_declName_2501_);
v___x_2524_ = l_Lean_mkPrivateName(v_____do__lift_2504_, v_declName_2501_);
v___x_2525_ = lean_is_reserved_name(v_env_2503_, v___x_2524_);
v___y_2513_ = v___x_2525_;
goto v___jp_2512_;
}
else
{
lean_dec_ref(v_env_2503_);
v___y_2513_ = v___x_2523_;
goto v___jp_2512_;
}
v___jp_2512_:
{
if (v___y_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec(v_declName_2501_);
v___x_2514_ = lean_box(0);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
v___x_2515_ = lean_apply_8(v___f_2500_, v___x_2514_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, lean_box(0));
return v___x_2515_;
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec_ref(v___f_2500_);
v___x_2516_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2517_ = l_Lean_MessageData_ofConstName(v_declName_2501_, v___x_2502_);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2520_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
return v___x_2521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___boxed(lean_object* v___f_2526_, lean_object* v_declName_2527_, lean_object* v___x_2528_, lean_object* v_env_2529_, lean_object* v_____do__lift_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
uint8_t v___x_56275__boxed_2538_; lean_object* v_res_2539_; 
v___x_56275__boxed_2538_ = lean_unbox(v___x_2528_);
v_res_2539_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3(v___f_2526_, v_declName_2527_, v___x_56275__boxed_2538_, v_env_2529_, v_____do__lift_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v_____do__lift_2530_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(lean_object* v_t_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v___x_2543_; lean_object* v_infoState_2544_; uint8_t v_enabled_2545_; 
v___x_2543_ = lean_st_ref_get(v___y_2541_);
v_infoState_2544_ = lean_ctor_get(v___x_2543_, 7);
lean_inc_ref(v_infoState_2544_);
lean_dec(v___x_2543_);
v_enabled_2545_ = lean_ctor_get_uint8(v_infoState_2544_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2544_);
if (v_enabled_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec_ref(v_t_2540_);
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
else
{
lean_object* v___x_2548_; lean_object* v_infoState_2549_; lean_object* v_env_2550_; lean_object* v_nextMacroScope_2551_; lean_object* v_ngen_2552_; lean_object* v_auxDeclNGen_2553_; lean_object* v_traceState_2554_; lean_object* v_cache_2555_; lean_object* v_messages_2556_; lean_object* v_snapshotTasks_2557_; lean_object* v_newDecls_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2580_; 
v___x_2548_ = lean_st_ref_take(v___y_2541_);
v_infoState_2549_ = lean_ctor_get(v___x_2548_, 7);
v_env_2550_ = lean_ctor_get(v___x_2548_, 0);
v_nextMacroScope_2551_ = lean_ctor_get(v___x_2548_, 1);
v_ngen_2552_ = lean_ctor_get(v___x_2548_, 2);
v_auxDeclNGen_2553_ = lean_ctor_get(v___x_2548_, 3);
v_traceState_2554_ = lean_ctor_get(v___x_2548_, 4);
v_cache_2555_ = lean_ctor_get(v___x_2548_, 5);
v_messages_2556_ = lean_ctor_get(v___x_2548_, 6);
v_snapshotTasks_2557_ = lean_ctor_get(v___x_2548_, 8);
v_newDecls_2558_ = lean_ctor_get(v___x_2548_, 9);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2560_ = v___x_2548_;
v_isShared_2561_ = v_isSharedCheck_2580_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_newDecls_2558_);
lean_inc(v_snapshotTasks_2557_);
lean_inc(v_infoState_2549_);
lean_inc(v_messages_2556_);
lean_inc(v_cache_2555_);
lean_inc(v_traceState_2554_);
lean_inc(v_auxDeclNGen_2553_);
lean_inc(v_ngen_2552_);
lean_inc(v_nextMacroScope_2551_);
lean_inc(v_env_2550_);
lean_dec(v___x_2548_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2580_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
uint8_t v_enabled_2562_; lean_object* v_assignment_2563_; lean_object* v_lazyAssignment_2564_; lean_object* v_trees_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2579_; 
v_enabled_2562_ = lean_ctor_get_uint8(v_infoState_2549_, sizeof(void*)*3);
v_assignment_2563_ = lean_ctor_get(v_infoState_2549_, 0);
v_lazyAssignment_2564_ = lean_ctor_get(v_infoState_2549_, 1);
v_trees_2565_ = lean_ctor_get(v_infoState_2549_, 2);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_infoState_2549_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2567_ = v_infoState_2549_;
v_isShared_2568_ = v_isSharedCheck_2579_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_trees_2565_);
lean_inc(v_lazyAssignment_2564_);
lean_inc(v_assignment_2563_);
lean_dec(v_infoState_2549_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2579_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = l_Lean_PersistentArray_push___redArg(v_trees_2565_, v_t_2540_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 2, v___x_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_assignment_2563_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_lazyAssignment_2564_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v___x_2569_);
lean_ctor_set_uint8(v_reuseFailAlloc_2578_, sizeof(void*)*3, v_enabled_2562_);
v___x_2571_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2573_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 7, v___x_2571_);
v___x_2573_ = v___x_2560_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_env_2550_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_nextMacroScope_2551_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_ngen_2552_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_auxDeclNGen_2553_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v_traceState_2554_);
lean_ctor_set(v_reuseFailAlloc_2577_, 5, v_cache_2555_);
lean_ctor_set(v_reuseFailAlloc_2577_, 6, v_messages_2556_);
lean_ctor_set(v_reuseFailAlloc_2577_, 7, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2577_, 8, v_snapshotTasks_2557_);
lean_ctor_set(v_reuseFailAlloc_2577_, 9, v_newDecls_2558_);
v___x_2573_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = lean_st_ref_set(v___y_2541_, v___x_2573_);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
return v___x_2576_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_t_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v_t_2581_, v___y_2582_);
lean_dec(v___y_2582_);
return v_res_2584_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_unsigned_to_nat(32u);
v___x_2586_ = lean_mk_empty_array_with_capacity(v___x_2585_);
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1(void){
_start:
{
size_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2588_ = ((size_t)5ULL);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_unsigned_to_nat(32u);
v___x_2591_ = lean_mk_empty_array_with_capacity(v___x_2590_);
v___x_2592_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0);
v___x_2593_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v___x_2591_);
lean_ctor_set(v___x_2593_, 2, v___x_2589_);
lean_ctor_set(v___x_2593_, 3, v___x_2589_);
lean_ctor_set_usize(v___x_2593_, 4, v___x_2588_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(lean_object* v_t_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; lean_object* v_infoState_2603_; uint8_t v_enabled_2604_; 
v___x_2602_ = lean_st_ref_get(v___y_2600_);
v_infoState_2603_ = lean_ctor_get(v___x_2602_, 7);
lean_inc_ref(v_infoState_2603_);
lean_dec(v___x_2602_);
v_enabled_2604_ = lean_ctor_get_uint8(v_infoState_2603_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2603_);
if (v_enabled_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec_ref(v_t_2594_);
v___x_2605_ = lean_box(0);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1);
v___x_2608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_t_2594_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v___x_2608_, v___y_2600_);
return v___x_2609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___boxed(lean_object* v_t_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(v_t_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__4(lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
if (lean_obj_tag(v_a_2619_) == 0)
{
lean_object* v___x_2621_; 
v___x_2621_ = l_List_reverse___redArg(v_a_2620_);
return v___x_2621_;
}
else
{
lean_object* v_head_2622_; lean_object* v_tail_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2632_; 
v_head_2622_ = lean_ctor_get(v_a_2619_, 0);
v_tail_2623_ = lean_ctor_get(v_a_2619_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2619_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2625_ = v_a_2619_;
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_tail_2623_);
lean_inc(v_head_2622_);
lean_dec(v_a_2619_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2629_; 
v___x_2627_ = l_Lean_mkLevelParam(v_head_2622_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 1, v_a_2620_);
lean_ctor_set(v___x_2625_, 0, v___x_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_a_2620_);
v___x_2629_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
v_a_2619_ = v_tail_2623_;
v_a_2620_ = v___x_2629_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0(void){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0);
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1);
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
lean_ctor_set(v___x_2638_, 2, v___x_2637_);
lean_ctor_set(v___x_2638_, 3, v___x_2637_);
lean_ctor_set(v___x_2638_, 4, v___x_2636_);
lean_ctor_set(v___x_2638_, 5, v___x_2636_);
lean_ctor_set(v___x_2638_, 6, v___x_2636_);
lean_ctor_set(v___x_2638_, 7, v___x_2636_);
lean_ctor_set(v___x_2638_, 8, v___x_2636_);
lean_ctor_set(v___x_2638_, 9, v___x_2636_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = lean_unsigned_to_nat(32u);
v___x_2640_ = lean_mk_empty_array_with_capacity(v___x_2639_);
v___x_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
return v___x_2641_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4(void){
_start:
{
size_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2642_ = ((size_t)5ULL);
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_unsigned_to_nat(32u);
v___x_2645_ = lean_mk_empty_array_with_capacity(v___x_2644_);
v___x_2646_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3);
v___x_2647_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
lean_ctor_set(v___x_2647_, 1, v___x_2645_);
lean_ctor_set(v___x_2647_, 2, v___x_2643_);
lean_ctor_set(v___x_2647_, 3, v___x_2643_);
lean_ctor_set_usize(v___x_2647_, 4, v___x_2642_);
return v___x_2647_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = lean_box(1);
v___x_2649_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4);
v___x_2650_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1);
v___x_2651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
lean_ctor_set(v___x_2651_, 1, v___x_2649_);
lean_ctor_set(v___x_2651_, 2, v___x_2648_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__6));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9(void){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__8));
v___x_2657_ = l_Lean_stringToMessageData(v___x_2656_);
return v___x_2657_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__10));
v___x_2660_ = l_Lean_stringToMessageData(v___x_2659_);
return v___x_2660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__12));
v___x_2663_ = l_Lean_stringToMessageData(v___x_2662_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__14));
v___x_2666_ = l_Lean_stringToMessageData(v___x_2665_);
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17(void){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2668_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__16));
v___x_2669_ = l_Lean_stringToMessageData(v___x_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(lean_object* v_msg_2670_, lean_object* v_declHint_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; lean_object* v_env_2675_; uint8_t v___x_2676_; 
v___x_2674_ = lean_st_ref_get(v___y_2672_);
v_env_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc_ref(v_env_2675_);
lean_dec(v___x_2674_);
v___x_2676_ = l_Lean_Name_isAnonymous(v_declHint_2671_);
if (v___x_2676_ == 0)
{
uint8_t v_isExporting_2677_; 
v_isExporting_2677_ = lean_ctor_get_uint8(v_env_2675_, sizeof(void*)*8);
if (v_isExporting_2677_ == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref(v_env_2675_);
lean_dec(v_declHint_2671_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v_msg_2670_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; uint8_t v___x_2680_; 
lean_inc_ref(v_env_2675_);
v___x_2679_ = l_Lean_Environment_setExporting(v_env_2675_, v___x_2676_);
lean_inc(v_declHint_2671_);
lean_inc_ref(v___x_2679_);
v___x_2680_ = l_Lean_Environment_contains(v___x_2679_, v_declHint_2671_, v_isExporting_2677_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; 
lean_dec_ref(v___x_2679_);
lean_dec_ref(v_env_2675_);
lean_dec(v_declHint_2671_);
v___x_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2681_, 0, v_msg_2670_);
return v___x_2681_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v_c_2687_; lean_object* v___x_2688_; 
v___x_2682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2);
v___x_2683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5);
v___x_2684_ = l_Lean_Options_empty;
v___x_2685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2679_);
lean_ctor_set(v___x_2685_, 1, v___x_2682_);
lean_ctor_set(v___x_2685_, 2, v___x_2683_);
lean_ctor_set(v___x_2685_, 3, v___x_2684_);
lean_inc(v_declHint_2671_);
v___x_2686_ = l_Lean_MessageData_ofConstName(v_declHint_2671_, v___x_2676_);
v_c_2687_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2687_, 0, v___x_2685_);
lean_ctor_set(v_c_2687_, 1, v___x_2686_);
v___x_2688_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2675_, v_declHint_2671_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec_ref(v_env_2675_);
lean_dec(v_declHint_2671_);
v___x_2689_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7);
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v_c_2687_);
v___x_2691_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_MessageData_note(v___x_2692_);
v___x_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2694_, 0, v_msg_2670_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
else
{
lean_object* v_val_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2731_; 
v_val_2696_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2698_ = v___x_2688_;
v_isShared_2699_ = v_isSharedCheck_2731_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_val_2696_);
lean_dec(v___x_2688_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2731_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v_mod_2703_; uint8_t v___x_2704_; 
v___x_2700_ = lean_box(0);
v___x_2701_ = l_Lean_Environment_header(v_env_2675_);
lean_dec_ref(v_env_2675_);
v___x_2702_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2701_);
v_mod_2703_ = lean_array_get(v___x_2700_, v___x_2702_, v_val_2696_);
lean_dec(v_val_2696_);
lean_dec_ref(v___x_2702_);
v___x_2704_ = l_Lean_isPrivateName(v_declHint_2671_);
lean_dec(v_declHint_2671_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2705_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
lean_ctor_set(v___x_2706_, 1, v_c_2687_);
v___x_2707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_MessageData_ofName(v_mod_2703_);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2710_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = l_Lean_MessageData_note(v___x_2712_);
v___x_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2714_, 0, v_msg_2670_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2714_);
v___x_2716_ = v___x_2698_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v_c_2687_);
v___x_2720_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = l_Lean_MessageData_ofName(v_mod_2703_);
v___x_2723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = l_Lean_MessageData_note(v___x_2725_);
v___x_2727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_msg_2670_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2727_);
v___x_2729_ = v___x_2698_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2732_; 
lean_dec_ref(v_env_2675_);
lean_dec(v_declHint_2671_);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_msg_2670_);
return v___x_2732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___boxed(lean_object* v_msg_2733_, lean_object* v_declHint_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(v_msg_2733_, v_declHint_2734_, v___y_2735_);
lean_dec(v___y_2735_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(lean_object* v_msg_2738_, lean_object* v_declHint_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2757_; 
v___x_2747_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(v_msg_2738_, v_declHint_2739_, v___y_2745_);
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2757_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2757_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2752_ = l_Lean_unknownIdentifierMessageTag;
v___x_2753_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
lean_ctor_set(v___x_2753_, 1, v_a_2748_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2753_);
v___x_2755_ = v___x_2750_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44___boxed(lean_object* v_msg_2758_, lean_object* v_declHint_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(v_msg_2758_, v_declHint_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(lean_object* v_ref_2768_, lean_object* v_msg_2769_, lean_object* v_declHint_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; lean_object* v_a_2779_; lean_object* v___x_2780_; 
v___x_2778_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(v_msg_2769_, v_declHint_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref(v___x_2778_);
v___x_2780_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_ref_2768_, v_a_2779_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg___boxed(lean_object* v_ref_2781_, lean_object* v_msg_2782_, lean_object* v_declHint_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(v_ref_2781_, v_msg_2782_, v_declHint_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v_ref_2781_);
return v_res_2791_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__0));
v___x_2794_ = l_Lean_stringToMessageData(v___x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(lean_object* v_ref_2795_, lean_object* v_constName_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___x_2804_; uint8_t v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2804_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1);
v___x_2805_ = 0;
lean_inc(v_constName_2796_);
v___x_2806_ = l_Lean_MessageData_ofConstName(v_constName_2796_, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2804_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2807_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(v_ref_2795_, v___x_2809_, v_constName_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___boxed(lean_object* v_ref_2811_, lean_object* v_constName_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(v_ref_2811_, v_constName_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v_ref_2811_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(lean_object* v_constName_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_ref_2829_; lean_object* v___x_2830_; 
v_ref_2829_ = lean_ctor_get(v___y_2826_, 5);
v___x_2830_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(v_ref_2829_, v_constName_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg___boxed(lean_object* v_constName_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(v_constName_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(lean_object* v_constName_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v_env_2849_; uint8_t v___x_2850_; lean_object* v___x_2851_; 
v___x_2848_ = lean_st_ref_get(v___y_2846_);
v_env_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc_ref(v_env_2849_);
lean_dec(v___x_2848_);
v___x_2850_ = 0;
lean_inc(v_constName_2840_);
v___x_2851_ = l_Lean_Environment_findConstVal_x3f(v_env_2849_, v_constName_2840_, v___x_2850_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2852_; 
v___x_2852_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(v_constName_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
return v___x_2852_;
}
else
{
lean_object* v_val_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_constName_2840_);
v_val_2853_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2851_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_val_2853_);
lean_dec(v___x_2851_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
lean_ctor_set_tag(v___x_2855_, 0);
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_val_2853_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3___boxed(lean_object* v_constName_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(v_constName_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(lean_object* v_constName_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
lean_inc(v_constName_2870_);
v___x_2878_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(v_constName_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2890_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2890_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2890_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_levelParams_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2888_; 
v_levelParams_2883_ = lean_ctor_get(v_a_2879_, 1);
lean_inc(v_levelParams_2883_);
lean_dec(v_a_2879_);
v___x_2884_ = lean_box(0);
v___x_2885_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__4(v_levelParams_2883_, v___x_2884_);
v___x_2886_ = l_Lean_mkConst(v_constName_2870_, v___x_2885_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2886_);
v___x_2888_ = v___x_2881_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_constName_2870_);
v_a_2891_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2878_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2878_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1___boxed(lean_object* v_constName_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(v_constName_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
return v_res_2907_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2908_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0);
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
return v___x_2910_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2911_ = lean_box(1);
v___x_2912_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4);
v___x_2913_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1);
v___x_2914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
lean_ctor_set(v___x_2914_, 1, v___x_2912_);
lean_ctor_set(v___x_2914_, 2, v___x_2911_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0(uint8_t v___x_2915_, lean_object* v_declName_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_ref_2924_; lean_object* v___x_2925_; 
v_ref_2924_ = lean_ctor_get(v___y_2921_, 5);
v___x_2925_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(v_declName_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref(v___x_2925_);
v___x_2927_ = lean_box(0);
lean_inc(v_ref_2924_);
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
lean_ctor_set(v___x_2928_, 1, v_ref_2924_);
v___x_2929_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2);
v___x_2930_ = lean_box(0);
v___x_2931_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2931_, 0, v___x_2928_);
lean_ctor_set(v___x_2931_, 1, v___x_2929_);
lean_ctor_set(v___x_2931_, 2, v___x_2930_);
lean_ctor_set(v___x_2931_, 3, v_a_2926_);
lean_ctor_set_uint8(v___x_2931_, sizeof(void*)*4, v___x_2915_);
lean_ctor_set_uint8(v___x_2931_, sizeof(void*)*4 + 1, v___x_2915_);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
v___x_2933_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(v___x_2932_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
return v___x_2933_;
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
v_a_2934_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2925_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2925_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___boxed(lean_object* v___x_2942_, lean_object* v_declName_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
uint8_t v___x_57000__boxed_2951_; lean_object* v_res_2952_; 
v___x_57000__boxed_2951_ = lean_unbox(v___x_2942_);
v_res_2952_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0(v___x_57000__boxed_2951_, v_declName_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
return v_res_2952_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__0));
v___x_2955_ = l_Lean_stringToMessageData(v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2(lean_object* v_env_2956_, lean_object* v_declName_2957_, lean_object* v___f_2958_, lean_object* v_addInfo_2959_, lean_object* v_____r_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; uint8_t v___x_2970_; 
lean_inc(v_declName_2957_);
v___x_2968_ = l_Lean_mkPrivateName(v_env_2956_, v_declName_2957_);
v___x_2969_ = 1;
lean_inc(v___x_2968_);
v___x_2970_ = l_Lean_Environment_contains(v_env_2956_, v___x_2968_, v___x_2969_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_dec(v___x_2968_);
lean_dec_ref(v_addInfo_2959_);
lean_dec(v_declName_2957_);
v___x_2971_ = lean_box(0);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2961_);
v___x_2972_ = lean_apply_8(v___f_2958_, v___x_2971_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, lean_box(0));
return v___x_2972_;
}
else
{
lean_object* v___x_2973_; 
lean_dec_ref(v___f_2958_);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2961_);
v___x_2973_ = lean_apply_8(v_addInfo_2959_, v___x_2968_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, lean_box(0));
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
lean_dec_ref(v___x_2973_);
v___x_2974_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1);
v___x_2975_ = l_Lean_MessageData_ofConstName(v_declName_2957_, v___x_2969_);
v___x_2976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2974_);
lean_ctor_set(v___x_2976_, 1, v___x_2975_);
v___x_2977_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2978_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
return v___x_2979_;
}
else
{
lean_dec(v_declName_2957_);
return v___x_2973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___boxed(lean_object* v_env_2980_, lean_object* v_declName_2981_, lean_object* v___f_2982_, lean_object* v_addInfo_2983_, lean_object* v_____r_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2(v_env_2980_, v_declName_2981_, v___f_2982_, v_addInfo_2983_, v_____r_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4(lean_object* v___f_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v___x_3001_; lean_object* v_env_3002_; lean_object* v___x_3003_; 
v___x_3001_ = lean_st_ref_get(v___y_2999_);
v_env_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc_ref(v_env_3002_);
lean_dec(v___x_3001_);
v___x_3003_ = lean_apply_8(v___f_2993_, v_env_3002_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, lean_box(0));
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4___boxed(lean_object* v___f_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4(v___f_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v_res_3012_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__0));
v___x_3015_ = l_Lean_stringToMessageData(v___x_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1(lean_object* v_declName_3016_, lean_object* v_env_3017_, lean_object* v_addInfo_3018_, lean_object* v_____r_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_private_to_user_name(v_declName_3016_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_dec_ref(v_addInfo_3018_);
lean_dec_ref(v_env_3017_);
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
else
{
lean_object* v_val_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3047_; 
v_val_3030_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3032_ = v___x_3027_;
v_isShared_3033_ = v_isSharedCheck_3047_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_val_3030_);
lean_dec(v___x_3027_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3047_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
uint8_t v___x_3034_; uint8_t v___x_3035_; 
v___x_3034_ = 1;
lean_inc(v_val_3030_);
v___x_3035_ = l_Lean_Environment_contains(v_env_3017_, v_val_3030_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3038_; 
lean_dec(v_val_3030_);
lean_dec_ref(v_addInfo_3018_);
v___x_3036_ = lean_box(0);
if (v_isShared_3033_ == 0)
{
lean_ctor_set_tag(v___x_3032_, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3036_);
v___x_3038_ = v___x_3032_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
else
{
lean_object* v___x_3040_; 
lean_del_object(v___x_3032_);
lean_inc(v___y_3025_);
lean_inc_ref(v___y_3024_);
lean_inc(v___y_3023_);
lean_inc_ref(v___y_3022_);
lean_inc(v___y_3021_);
lean_inc_ref(v___y_3020_);
lean_inc(v_val_3030_);
v___x_3040_ = lean_apply_8(v_addInfo_3018_, v_val_3030_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, lean_box(0));
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec_ref(v___x_3040_);
v___x_3041_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1);
v___x_3042_ = l_Lean_MessageData_ofConstName(v_val_3030_, v___x_3034_);
v___x_3043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_3045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_3045_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
return v___x_3046_;
}
else
{
lean_dec(v_val_3030_);
return v___x_3040_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___boxed(lean_object* v_declName_3048_, lean_object* v_env_3049_, lean_object* v_addInfo_3050_, lean_object* v_____r_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1(v_declName_3048_, v_env_3049_, v_addInfo_3050_, v_____r_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(lean_object* v_env_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v___x_3064_; lean_object* v_nextMacroScope_3065_; lean_object* v_ngen_3066_; lean_object* v_auxDeclNGen_3067_; lean_object* v_traceState_3068_; lean_object* v_messages_3069_; lean_object* v_infoState_3070_; lean_object* v_snapshotTasks_3071_; lean_object* v_newDecls_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3098_; 
v___x_3064_ = lean_st_ref_take(v___y_3062_);
v_nextMacroScope_3065_ = lean_ctor_get(v___x_3064_, 1);
v_ngen_3066_ = lean_ctor_get(v___x_3064_, 2);
v_auxDeclNGen_3067_ = lean_ctor_get(v___x_3064_, 3);
v_traceState_3068_ = lean_ctor_get(v___x_3064_, 4);
v_messages_3069_ = lean_ctor_get(v___x_3064_, 6);
v_infoState_3070_ = lean_ctor_get(v___x_3064_, 7);
v_snapshotTasks_3071_ = lean_ctor_get(v___x_3064_, 8);
v_newDecls_3072_ = lean_ctor_get(v___x_3064_, 9);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; lean_object* v_unused_3100_; 
v_unused_3099_ = lean_ctor_get(v___x_3064_, 5);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v___x_3064_, 0);
lean_dec(v_unused_3100_);
v___x_3074_ = v___x_3064_;
v_isShared_3075_ = v_isSharedCheck_3098_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_newDecls_3072_);
lean_inc(v_snapshotTasks_3071_);
lean_inc(v_infoState_3070_);
lean_inc(v_messages_3069_);
lean_inc(v_traceState_3068_);
lean_inc(v_auxDeclNGen_3067_);
lean_inc(v_ngen_3066_);
lean_inc(v_nextMacroScope_3065_);
lean_dec(v___x_3064_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3098_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 5, v___x_3076_);
lean_ctor_set(v___x_3074_, 0, v_env_3060_);
v___x_3078_ = v___x_3074_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_env_3060_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_nextMacroScope_3065_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v_ngen_3066_);
lean_ctor_set(v_reuseFailAlloc_3097_, 3, v_auxDeclNGen_3067_);
lean_ctor_set(v_reuseFailAlloc_3097_, 4, v_traceState_3068_);
lean_ctor_set(v_reuseFailAlloc_3097_, 5, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3097_, 6, v_messages_3069_);
lean_ctor_set(v_reuseFailAlloc_3097_, 7, v_infoState_3070_);
lean_ctor_set(v_reuseFailAlloc_3097_, 8, v_snapshotTasks_3071_);
lean_ctor_set(v_reuseFailAlloc_3097_, 9, v_newDecls_3072_);
v___x_3078_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v_mctx_3081_; lean_object* v_zetaDeltaFVarIds_3082_; lean_object* v_postponed_3083_; lean_object* v_diag_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3095_; 
v___x_3079_ = lean_st_ref_set(v___y_3062_, v___x_3078_);
v___x_3080_ = lean_st_ref_take(v___y_3061_);
v_mctx_3081_ = lean_ctor_get(v___x_3080_, 0);
v_zetaDeltaFVarIds_3082_ = lean_ctor_get(v___x_3080_, 2);
v_postponed_3083_ = lean_ctor_get(v___x_3080_, 3);
v_diag_3084_ = lean_ctor_get(v___x_3080_, 4);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3095_ == 0)
{
lean_object* v_unused_3096_; 
v_unused_3096_ = lean_ctor_get(v___x_3080_, 1);
lean_dec(v_unused_3096_);
v___x_3086_ = v___x_3080_;
v_isShared_3087_ = v_isSharedCheck_3095_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_diag_3084_);
lean_inc(v_postponed_3083_);
lean_inc(v_zetaDeltaFVarIds_3082_);
lean_inc(v_mctx_3081_);
lean_dec(v___x_3080_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3095_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3088_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 1, v___x_3088_);
v___x_3090_ = v___x_3086_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_mctx_3081_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3088_);
lean_ctor_set(v_reuseFailAlloc_3094_, 2, v_zetaDeltaFVarIds_3082_);
lean_ctor_set(v_reuseFailAlloc_3094_, 3, v_postponed_3083_);
lean_ctor_set(v_reuseFailAlloc_3094_, 4, v_diag_3084_);
v___x_3090_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = lean_st_ref_set(v___y_3061_, v___x_3090_);
v___x_3092_ = lean_box(0);
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
return v___x_3093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_env_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec(v___y_3102_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(lean_object* v_env_3106_, lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; lean_object* v_env_3116_; lean_object* v_a_3118_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3115_ = lean_st_ref_get(v___y_3113_);
v_env_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc_ref(v_env_3116_);
lean_dec(v___x_3115_);
v___x_3128_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3106_, v___y_3111_, v___y_3113_);
lean_dec_ref(v___x_3128_);
lean_inc(v___y_3113_);
lean_inc_ref(v___y_3112_);
lean_inc(v___y_3111_);
lean_inc_ref(v___y_3110_);
lean_inc(v___y_3109_);
lean_inc_ref(v___y_3108_);
v___x_3129_ = lean_apply_7(v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, lean_box(0));
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref(v___x_3129_);
v___x_3131_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3116_, v___y_3111_, v___y_3113_);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v___x_3131_, 0);
lean_dec(v_unused_3139_);
v___x_3133_ = v___x_3131_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_dec(v___x_3131_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v_a_3130_);
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3130_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
else
{
lean_object* v_a_3140_; 
v_a_3140_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3129_);
v_a_3118_ = v_a_3140_;
goto v___jp_3117_;
}
v___jp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
v___x_3119_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3116_, v___y_3111_, v___y_3113_);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v___x_3119_, 0);
lean_dec(v_unused_3127_);
v___x_3121_ = v___x_3119_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_dec(v___x_3119_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set_tag(v___x_3121_, 1);
lean_ctor_set(v___x_3121_, 0, v_a_3118_);
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3118_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg___boxed(lean_object* v_env_3141_, lean_object* v_x_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3141_, v_x_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(lean_object* v_declName_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v___x_3162_; lean_object* v_env_3163_; uint8_t v___x_3164_; lean_object* v_addInfo_3165_; lean_object* v_env_3166_; lean_object* v___f_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___f_3170_; uint8_t v___x_3171_; uint8_t v___x_3172_; 
v___x_3162_ = lean_st_ref_get(v___y_3160_);
v_env_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc_ref(v_env_3163_);
lean_dec(v___x_3162_);
v___x_3164_ = 0;
v_addInfo_3165_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___closed__0));
v_env_3166_ = l_Lean_Environment_setExporting(v_env_3163_, v___x_3164_);
lean_inc_ref_n(v_env_3166_, 4);
lean_inc_n(v_declName_3154_, 4);
v___f_3167_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3167_, 0, v_declName_3154_);
lean_closure_set(v___f_3167_, 1, v_env_3166_);
lean_closure_set(v___f_3167_, 2, v_addInfo_3165_);
v___f_3168_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3168_, 0, v_env_3166_);
lean_closure_set(v___f_3168_, 1, v_declName_3154_);
lean_closure_set(v___f_3168_, 2, v___f_3167_);
lean_closure_set(v___f_3168_, 3, v_addInfo_3165_);
v___x_3169_ = lean_box(v___x_3164_);
lean_inc_ref(v___f_3168_);
v___f_3170_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___boxed), 12, 4);
lean_closure_set(v___f_3170_, 0, v___f_3168_);
lean_closure_set(v___f_3170_, 1, v_declName_3154_);
lean_closure_set(v___f_3170_, 2, v___x_3169_);
lean_closure_set(v___f_3170_, 3, v_env_3166_);
v___x_3171_ = 1;
v___x_3172_ = l_Lean_Environment_contains(v_env_3166_, v_declName_3154_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___f_3173_; lean_object* v___x_3174_; 
lean_dec_ref(v___f_3168_);
lean_dec(v_declName_3154_);
v___f_3173_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4___boxed), 8, 1);
lean_closure_set(v___f_3173_, 0, v___f_3170_);
v___x_3174_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3166_, v___f_3173_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
return v___x_3174_;
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___f_3177_; lean_object* v___x_3178_; 
v___x_3175_ = lean_box(v___x_3171_);
v___x_3176_ = lean_box(v___x_3164_);
lean_inc_ref(v_env_3166_);
v___f_3177_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___boxed), 14, 7);
lean_closure_set(v___f_3177_, 0, v_addInfo_3165_);
lean_closure_set(v___f_3177_, 1, v_declName_3154_);
lean_closure_set(v___f_3177_, 2, v___x_3175_);
lean_closure_set(v___f_3177_, 3, v___f_3168_);
lean_closure_set(v___f_3177_, 4, v___x_3176_);
lean_closure_set(v___f_3177_, 5, v_env_3166_);
lean_closure_set(v___f_3177_, 6, v___f_3170_);
v___x_3178_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3166_, v___f_3177_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
return v___x_3178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___boxed(lean_object* v_declName_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(v_declName_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
return v_res_3187_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__1));
v___x_3192_ = l_Lean_MessageData_ofFormat(v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0(lean_object* v___x_3193_, uint8_t v___x_3194_, uint8_t v___x_3195_, lean_object* v_xs_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; 
lean_inc(v___x_3193_);
v___x_3204_ = l_Lean_Elab_Term_elabType(v___x_3193_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2);
v___x_3207_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_3205_, v___x_3193_, v___x_3206_, v___y_3198_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v___x_3208_; lean_object* v_fst_3209_; lean_object* v_snd_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v___x_3207_);
v___x_3208_ = l_Array_unzip___redArg(v_xs_3196_);
v_fst_3209_ = lean_ctor_get(v___x_3208_, 0);
v_snd_3210_ = lean_ctor_get(v___x_3208_, 1);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3212_ = v___x_3208_;
v_isShared_3213_ = v_isSharedCheck_3235_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_snd_3210_);
lean_inc(v_fst_3209_);
lean_dec(v___x_3208_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3235_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
uint8_t v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = 1;
v___x_3215_ = l_Lean_Meta_mkForallFVars(v_snd_3210_, v_a_3205_, v___x_3194_, v___x_3195_, v___x_3195_, v___x_3214_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v_snd_3210_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3226_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3218_ = v___x_3215_;
v_isShared_3219_ = v_isSharedCheck_3226_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3215_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3226_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 1, v_fst_3209_);
lean_ctor_set(v___x_3212_, 0, v_a_3216_);
v___x_3221_ = v___x_3212_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3216_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_fst_3209_);
v___x_3221_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3223_; 
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v___x_3221_);
v___x_3223_ = v___x_3218_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_del_object(v___x_3212_);
lean_dec(v_fst_3209_);
v_a_3227_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3215_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3215_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec(v_a_3205_);
v_a_3236_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3207_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3207_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec(v___x_3193_);
v_a_3244_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3204_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3204_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___boxed(lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v___x_3254_, lean_object* v_xs_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
uint8_t v___x_57456__boxed_3263_; uint8_t v___x_57457__boxed_3264_; lean_object* v_res_3265_; 
v___x_57456__boxed_3263_ = lean_unbox(v___x_3253_);
v___x_57457__boxed_3264_ = lean_unbox(v___x_3254_);
v_res_3265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0(v___x_3252_, v___x_57456__boxed_3263_, v___x_57457__boxed_3264_, v_xs_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec_ref(v_xs_3255_);
return v_res_3265_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(lean_object* v_declName_3266_, lean_object* v_as_3267_, size_t v_i_3268_, size_t v_stop_3269_){
_start:
{
uint8_t v___x_3270_; 
v___x_3270_ = lean_usize_dec_eq(v_i_3268_, v_stop_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; lean_object* v_declName_3272_; uint8_t v___x_3273_; 
v___x_3271_ = lean_array_uget_borrowed(v_as_3267_, v_i_3268_);
v_declName_3272_ = lean_ctor_get(v___x_3271_, 3);
v___x_3273_ = lean_name_eq(v_declName_3272_, v_declName_3266_);
if (v___x_3273_ == 0)
{
size_t v___x_3274_; size_t v___x_3275_; 
v___x_3274_ = ((size_t)1ULL);
v___x_3275_ = lean_usize_add(v_i_3268_, v___x_3274_);
v_i_3268_ = v___x_3275_;
goto _start;
}
else
{
return v___x_3273_;
}
}
else
{
uint8_t v___x_3277_; 
v___x_3277_ = 0;
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6___boxed(lean_object* v_declName_3278_, lean_object* v_as_3279_, lean_object* v_i_3280_, lean_object* v_stop_3281_){
_start:
{
size_t v_i_boxed_3282_; size_t v_stop_boxed_3283_; uint8_t v_res_3284_; lean_object* v_r_3285_; 
v_i_boxed_3282_ = lean_unbox_usize(v_i_3280_);
lean_dec(v_i_3280_);
v_stop_boxed_3283_ = lean_unbox_usize(v_stop_3281_);
lean_dec(v_stop_3281_);
v_res_3284_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(v_declName_3278_, v_as_3279_, v_i_boxed_3282_, v_stop_boxed_3283_);
lean_dec_ref(v_as_3279_);
lean_dec(v_declName_3278_);
v_r_3285_ = lean_box(v_res_3284_);
return v_r_3285_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__0));
v___x_3288_ = l_Lean_stringToMessageData(v___x_3287_);
return v___x_3288_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__8));
v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(uint8_t v___x_3310_, lean_object* v_as_3311_, size_t v_sz_3312_, size_t v_i_3313_, lean_object* v_b_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v_a_3323_; uint8_t v___x_3327_; 
v___x_3327_ = lean_usize_dec_lt(v_i_3313_, v_sz_3312_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_b_3314_);
return v___x_3328_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v_a_3331_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v_valStx_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; uint8_t v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; uint8_t v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; uint8_t v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; uint8_t v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; uint8_t v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; uint8_t v___y_3516_; lean_object* v___y_3517_; uint8_t v___y_3518_; lean_object* v___y_3519_; lean_object* v_declName_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; uint8_t v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; uint8_t v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; uint8_t v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; uint8_t v___y_3565_; lean_object* v___y_3566_; uint8_t v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; uint8_t v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; uint8_t v___y_3581_; uint8_t v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; uint8_t v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; uint8_t v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3632_; lean_object* v_attrs_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3669_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = lean_unsigned_to_nat(1u);
v_a_3331_ = lean_array_uget_borrowed(v_as_3311_, v_i_3313_);
v___x_3684_ = l_Lean_Syntax_getArg(v_a_3331_, v___x_3329_);
v___x_3685_ = l_Lean_Syntax_getOptional_x3f(v___x_3684_);
lean_dec(v___x_3684_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v___x_3686_; 
v___x_3686_ = lean_box(0);
v___y_3669_ = v___x_3686_;
goto v___jp_3668_;
}
else
{
lean_object* v_val_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3696_; 
v_val_3687_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3689_ = v___x_3685_;
v_isShared_3690_ = v_isSharedCheck_3696_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_val_3687_);
lean_dec(v___x_3685_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3696_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
v___x_3691_ = lean_box(v___x_3310_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_val_3687_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3692_);
v___x_3694_ = v___x_3689_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
v___y_3669_ = v___x_3694_;
goto v___jp_3668_;
}
}
}
v___jp_3332_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3350_ = lean_unsigned_to_nat(3u);
v___x_3351_ = l_Lean_Syntax_getArg(v_a_3331_, v___x_3350_);
v___x_3352_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(v___x_3351_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref(v___x_3352_);
v___x_3354_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3354_, 0, v___y_3342_);
lean_ctor_set(v___x_3354_, 1, v___y_3337_);
lean_ctor_set(v___x_3354_, 2, v___y_3334_);
lean_ctor_set(v___x_3354_, 3, v___y_3341_);
lean_ctor_set(v___x_3354_, 4, v___y_3333_);
lean_ctor_set(v___x_3354_, 5, v___y_3336_);
lean_ctor_set(v___x_3354_, 6, v___y_3340_);
lean_ctor_set(v___x_3354_, 7, v___y_3338_);
lean_ctor_set(v___x_3354_, 8, v___y_3335_);
lean_ctor_set(v___x_3354_, 9, v_valStx_3343_);
lean_ctor_set(v___x_3354_, 10, v_a_3353_);
lean_ctor_set(v___x_3354_, 11, v___y_3339_);
v___x_3355_ = lean_array_push(v_b_3314_, v___x_3354_);
v_a_3323_ = v___x_3355_;
goto v___jp_3322_;
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec(v_valStx_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v_b_3314_);
v_a_3356_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3352_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3352_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
v___jp_3364_:
{
lean_object* v___x_3381_; 
lean_inc(v___y_3374_);
v___x_3381_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3381_) == 0)
{
uint8_t v___x_3382_; lean_object* v___x_3383_; 
lean_dec_ref(v___x_3381_);
v___x_3382_ = 2;
lean_inc_ref(v___y_3369_);
lean_inc(v___y_3374_);
v___x_3383_ = l_Lean_Elab_Term_applyAttributesAt(v___y_3374_, v___y_3369_, v___x_3382_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref(v___x_3383_);
lean_inc(v___y_3374_);
v___x_3384_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(v___y_3374_, v___y_3368_, v___y_3373_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___f_3391_; lean_object* v___x_3392_; 
lean_dec_ref(v___x_3384_);
v___x_3385_ = l_Lean_Syntax_getArg(v___y_3368_, v___x_3330_);
v___x_3386_ = l_Lean_Syntax_getArgs(v___x_3385_);
v___x_3387_ = l_Lean_Syntax_getArg(v___y_3368_, v___y_3372_);
v___x_3388_ = l_Lean_Elab_Term_expandOptType(v___y_3373_, v___x_3387_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_box(v___y_3365_);
v___x_3390_ = lean_box(v___x_3327_);
v___f_3391_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3391_, 0, v___x_3388_);
lean_closure_set(v___f_3391_, 1, v___x_3389_);
lean_closure_set(v___f_3391_, 2, v___x_3390_);
v___x_3392_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___x_3386_, v___f_3391_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v_fst_3394_; lean_object* v_snd_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref(v___x_3392_);
v_fst_3394_ = lean_ctor_get(v_a_3393_, 0);
lean_inc_n(v_fst_3394_, 2);
v_snd_3395_ = lean_ctor_get(v_a_3393_, 1);
lean_inc(v_snd_3395_);
lean_dec(v_a_3393_);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_fst_3394_);
v___x_3397_ = 2;
v___x_3398_ = lean_box(0);
v___x_3399_ = l_Lean_Meta_mkFreshExprMVar(v___x_3396_, v___x_3397_, v___x_3398_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3399_) == 0)
{
if (v___y_3371_ == 0)
{
lean_object* v_a_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref(v___x_3399_);
v___x_3401_ = lean_unsigned_to_nat(3u);
v___x_3402_ = l_Lean_Syntax_getArg(v___y_3368_, v___x_3401_);
v___x_3403_ = lean_box(v___x_3327_);
v___x_3404_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed), 5, 3);
lean_closure_set(v___x_3404_, 0, v___y_3368_);
lean_closure_set(v___x_3404_, 1, v___x_3402_);
lean_closure_set(v___x_3404_, 2, v___x_3403_);
v___x_3405_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_3404_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref(v___x_3405_);
v___y_3333_ = v___y_3366_;
v___y_3334_ = v___y_3367_;
v___y_3335_ = v_a_3400_;
v___y_3336_ = v_snd_3395_;
v___y_3337_ = v___y_3369_;
v___y_3338_ = v_fst_3394_;
v___y_3339_ = v___y_3370_;
v___y_3340_ = v___x_3385_;
v___y_3341_ = v___y_3374_;
v___y_3342_ = v___y_3373_;
v_valStx_3343_ = v_a_3406_;
v___y_3344_ = v___y_3375_;
v___y_3345_ = v___y_3376_;
v___y_3346_ = v___y_3377_;
v___y_3347_ = v___y_3378_;
v___y_3348_ = v___y_3379_;
v___y_3349_ = v___y_3380_;
goto v___jp_3332_;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec(v_a_3400_);
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v___x_3385_);
lean_dec(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v_b_3314_);
v_a_3407_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3405_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3405_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v_a_3415_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3415_);
lean_dec_ref(v___x_3399_);
v___x_3416_ = lean_unsigned_to_nat(4u);
v___x_3417_ = l_Lean_Syntax_getArg(v___y_3368_, v___x_3416_);
lean_dec(v___y_3368_);
v___y_3333_ = v___y_3366_;
v___y_3334_ = v___y_3367_;
v___y_3335_ = v_a_3415_;
v___y_3336_ = v_snd_3395_;
v___y_3337_ = v___y_3369_;
v___y_3338_ = v_fst_3394_;
v___y_3339_ = v___y_3370_;
v___y_3340_ = v___x_3385_;
v___y_3341_ = v___y_3374_;
v___y_3342_ = v___y_3373_;
v_valStx_3343_ = v___x_3417_;
v___y_3344_ = v___y_3375_;
v___y_3345_ = v___y_3376_;
v___y_3346_ = v___y_3377_;
v___y_3347_ = v___y_3378_;
v___y_3348_ = v___y_3379_;
v___y_3349_ = v___y_3380_;
goto v___jp_3332_;
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v_snd_3395_);
lean_dec(v_fst_3394_);
lean_dec(v___x_3385_);
lean_dec(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v_b_3314_);
v_a_3418_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3399_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3399_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec(v___x_3385_);
lean_dec(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v_b_3314_);
v_a_3426_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3392_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3392_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v_b_3314_);
v_a_3434_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3384_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3384_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v_b_3314_);
v_a_3442_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3383_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3383_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
lean_dec(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v_b_3314_);
v_a_3450_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3381_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3381_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
v___jp_3458_:
{
if (v___y_3476_ == 0)
{
v___y_3365_ = v___y_3459_;
v___y_3366_ = v___y_3466_;
v___y_3367_ = v___y_3460_;
v___y_3368_ = v___y_3468_;
v___y_3369_ = v___y_3462_;
v___y_3370_ = v___y_3463_;
v___y_3371_ = v___y_3473_;
v___y_3372_ = v___y_3472_;
v___y_3373_ = v___y_3464_;
v___y_3374_ = v___y_3474_;
v___y_3375_ = v___y_3465_;
v___y_3376_ = v___y_3461_;
v___y_3377_ = v___y_3469_;
v___y_3378_ = v___y_3470_;
v___y_3379_ = v___y_3467_;
v___y_3380_ = v___y_3475_;
goto v___jp_3364_;
}
else
{
lean_object* v_fileName_3477_; lean_object* v_fileMap_3478_; lean_object* v_options_3479_; lean_object* v_currRecDepth_3480_; lean_object* v_maxRecDepth_3481_; lean_object* v_ref_3482_; lean_object* v_currNamespace_3483_; lean_object* v_openDecls_3484_; lean_object* v_initHeartbeats_3485_; lean_object* v_maxHeartbeats_3486_; lean_object* v_quotContext_3487_; lean_object* v_currMacroScope_3488_; uint8_t v_diag_3489_; lean_object* v_cancelTk_x3f_3490_; uint8_t v_suppressElabErrors_3491_; lean_object* v_inheritedTraceOptions_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v_ref_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_fileName_3477_ = lean_ctor_get(v___y_3467_, 0);
v_fileMap_3478_ = lean_ctor_get(v___y_3467_, 1);
v_options_3479_ = lean_ctor_get(v___y_3467_, 2);
v_currRecDepth_3480_ = lean_ctor_get(v___y_3467_, 3);
v_maxRecDepth_3481_ = lean_ctor_get(v___y_3467_, 4);
v_ref_3482_ = lean_ctor_get(v___y_3467_, 5);
v_currNamespace_3483_ = lean_ctor_get(v___y_3467_, 6);
v_openDecls_3484_ = lean_ctor_get(v___y_3467_, 7);
v_initHeartbeats_3485_ = lean_ctor_get(v___y_3467_, 8);
v_maxHeartbeats_3486_ = lean_ctor_get(v___y_3467_, 9);
v_quotContext_3487_ = lean_ctor_get(v___y_3467_, 10);
v_currMacroScope_3488_ = lean_ctor_get(v___y_3467_, 11);
v_diag_3489_ = lean_ctor_get_uint8(v___y_3467_, sizeof(void*)*14);
v_cancelTk_x3f_3490_ = lean_ctor_get(v___y_3467_, 12);
v_suppressElabErrors_3491_ = lean_ctor_get_uint8(v___y_3467_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3492_ = lean_ctor_get(v___y_3467_, 13);
v___x_3493_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
lean_inc(v___y_3474_);
v___x_3494_ = l_Lean_MessageData_ofConstName(v___y_3474_, v___y_3471_);
v___x_3495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v_ref_3498_ = l_Lean_replaceRef(v___y_3464_, v_ref_3482_);
lean_inc_ref(v_inheritedTraceOptions_3492_);
lean_inc(v_cancelTk_x3f_3490_);
lean_inc(v_currMacroScope_3488_);
lean_inc(v_quotContext_3487_);
lean_inc(v_maxHeartbeats_3486_);
lean_inc(v_initHeartbeats_3485_);
lean_inc(v_openDecls_3484_);
lean_inc(v_currNamespace_3483_);
lean_inc(v_maxRecDepth_3481_);
lean_inc(v_currRecDepth_3480_);
lean_inc_ref(v_options_3479_);
lean_inc_ref(v_fileMap_3478_);
lean_inc_ref(v_fileName_3477_);
v___x_3499_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3499_, 0, v_fileName_3477_);
lean_ctor_set(v___x_3499_, 1, v_fileMap_3478_);
lean_ctor_set(v___x_3499_, 2, v_options_3479_);
lean_ctor_set(v___x_3499_, 3, v_currRecDepth_3480_);
lean_ctor_set(v___x_3499_, 4, v_maxRecDepth_3481_);
lean_ctor_set(v___x_3499_, 5, v_ref_3498_);
lean_ctor_set(v___x_3499_, 6, v_currNamespace_3483_);
lean_ctor_set(v___x_3499_, 7, v_openDecls_3484_);
lean_ctor_set(v___x_3499_, 8, v_initHeartbeats_3485_);
lean_ctor_set(v___x_3499_, 9, v_maxHeartbeats_3486_);
lean_ctor_set(v___x_3499_, 10, v_quotContext_3487_);
lean_ctor_set(v___x_3499_, 11, v_currMacroScope_3488_);
lean_ctor_set(v___x_3499_, 12, v_cancelTk_x3f_3490_);
lean_ctor_set(v___x_3499_, 13, v_inheritedTraceOptions_3492_);
lean_ctor_set_uint8(v___x_3499_, sizeof(void*)*14, v_diag_3489_);
lean_ctor_set_uint8(v___x_3499_, sizeof(void*)*14 + 1, v_suppressElabErrors_3491_);
v___x_3500_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_3497_, v___y_3465_, v___y_3461_, v___y_3469_, v___y_3470_, v___x_3499_, v___y_3475_);
lean_dec_ref(v___x_3499_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_dec_ref(v___x_3500_);
v___y_3365_ = v___y_3459_;
v___y_3366_ = v___y_3466_;
v___y_3367_ = v___y_3460_;
v___y_3368_ = v___y_3468_;
v___y_3369_ = v___y_3462_;
v___y_3370_ = v___y_3463_;
v___y_3371_ = v___y_3473_;
v___y_3372_ = v___y_3472_;
v___y_3373_ = v___y_3464_;
v___y_3374_ = v___y_3474_;
v___y_3375_ = v___y_3465_;
v___y_3376_ = v___y_3461_;
v___y_3377_ = v___y_3469_;
v___y_3378_ = v___y_3470_;
v___y_3379_ = v___y_3467_;
v___y_3380_ = v___y_3475_;
goto v___jp_3364_;
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec(v___y_3474_);
lean_dec(v___y_3468_);
lean_dec(v___y_3466_);
lean_dec(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3460_);
lean_dec_ref(v_b_3314_);
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
v___jp_3509_:
{
lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3527_ = lean_array_get_size(v_b_3314_);
v___x_3528_ = lean_nat_dec_lt(v___x_3329_, v___x_3527_);
if (v___x_3528_ == 0)
{
v___y_3459_ = v___y_3510_;
v___y_3460_ = v___y_3512_;
v___y_3461_ = v___y_3522_;
v___y_3462_ = v___y_3514_;
v___y_3463_ = v___y_3515_;
v___y_3464_ = v___y_3519_;
v___y_3465_ = v___y_3521_;
v___y_3466_ = v___y_3511_;
v___y_3467_ = v___y_3525_;
v___y_3468_ = v___y_3513_;
v___y_3469_ = v___y_3523_;
v___y_3470_ = v___y_3524_;
v___y_3471_ = v___y_3516_;
v___y_3472_ = v___y_3517_;
v___y_3473_ = v___y_3518_;
v___y_3474_ = v_declName_3520_;
v___y_3475_ = v___y_3526_;
v___y_3476_ = v___y_3516_;
goto v___jp_3458_;
}
else
{
if (v___x_3528_ == 0)
{
v___y_3459_ = v___y_3510_;
v___y_3460_ = v___y_3512_;
v___y_3461_ = v___y_3522_;
v___y_3462_ = v___y_3514_;
v___y_3463_ = v___y_3515_;
v___y_3464_ = v___y_3519_;
v___y_3465_ = v___y_3521_;
v___y_3466_ = v___y_3511_;
v___y_3467_ = v___y_3525_;
v___y_3468_ = v___y_3513_;
v___y_3469_ = v___y_3523_;
v___y_3470_ = v___y_3524_;
v___y_3471_ = v___y_3516_;
v___y_3472_ = v___y_3517_;
v___y_3473_ = v___y_3518_;
v___y_3474_ = v_declName_3520_;
v___y_3475_ = v___y_3526_;
v___y_3476_ = v___y_3516_;
goto v___jp_3458_;
}
else
{
size_t v___x_3529_; size_t v___x_3530_; uint8_t v___x_3531_; 
v___x_3529_ = ((size_t)0ULL);
v___x_3530_ = lean_usize_of_nat(v___x_3527_);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(v_declName_3520_, v_b_3314_, v___x_3529_, v___x_3530_);
v___y_3459_ = v___y_3510_;
v___y_3460_ = v___y_3512_;
v___y_3461_ = v___y_3522_;
v___y_3462_ = v___y_3514_;
v___y_3463_ = v___y_3515_;
v___y_3464_ = v___y_3519_;
v___y_3465_ = v___y_3521_;
v___y_3466_ = v___y_3511_;
v___y_3467_ = v___y_3525_;
v___y_3468_ = v___y_3513_;
v___y_3469_ = v___y_3523_;
v___y_3470_ = v___y_3524_;
v___y_3471_ = v___y_3516_;
v___y_3472_ = v___y_3517_;
v___y_3473_ = v___y_3518_;
v___y_3474_ = v_declName_3520_;
v___y_3475_ = v___y_3526_;
v___y_3476_ = v___x_3531_;
goto v___jp_3458_;
}
}
}
v___jp_3532_:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lean_mkPrivateName(v___y_3544_, v___y_3541_);
lean_dec_ref(v___y_3544_);
v___y_3510_ = v___y_3533_;
v___y_3511_ = v___y_3540_;
v___y_3512_ = v___y_3535_;
v___y_3513_ = v___y_3543_;
v___y_3514_ = v___y_3536_;
v___y_3515_ = v___y_3537_;
v___y_3516_ = v___y_3546_;
v___y_3517_ = v___y_3549_;
v___y_3518_ = v___y_3548_;
v___y_3519_ = v___y_3539_;
v_declName_3520_ = v___x_3551_;
v___y_3521_ = v___y_3545_;
v___y_3522_ = v___y_3547_;
v___y_3523_ = v___y_3550_;
v___y_3524_ = v___y_3538_;
v___y_3525_ = v___y_3534_;
v___y_3526_ = v___y_3542_;
goto v___jp_3509_;
}
v___jp_3552_:
{
lean_object* v___x_3570_; lean_object* v_env_3571_; lean_object* v___x_3572_; uint8_t v_isModule_3573_; lean_object* v___x_3574_; 
v___x_3570_ = lean_st_ref_get(v___y_3562_);
v_env_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc_ref(v_env_3571_);
lean_dec(v___x_3570_);
v___x_3572_ = l_Lean_Environment_header(v_env_3571_);
v_isModule_3573_ = lean_ctor_get_uint8(v___x_3572_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3572_);
lean_inc(v___y_3555_);
v___x_3574_ = l_Lean_Name_append(v___y_3569_, v___y_3555_);
if (v_isModule_3573_ == 0)
{
lean_dec_ref(v_env_3571_);
v___y_3510_ = v___y_3553_;
v___y_3511_ = v___y_3560_;
v___y_3512_ = v___y_3555_;
v___y_3513_ = v___y_3561_;
v___y_3514_ = v___y_3556_;
v___y_3515_ = v___y_3557_;
v___y_3516_ = v___y_3565_;
v___y_3517_ = v___y_3566_;
v___y_3518_ = v___y_3567_;
v___y_3519_ = v___y_3559_;
v_declName_3520_ = v___x_3574_;
v___y_3521_ = v___y_3563_;
v___y_3522_ = v___y_3564_;
v___y_3523_ = v___y_3568_;
v___y_3524_ = v___y_3558_;
v___y_3525_ = v___y_3554_;
v___y_3526_ = v___y_3562_;
goto v___jp_3509_;
}
else
{
uint8_t v_isExporting_3575_; 
v_isExporting_3575_ = lean_ctor_get_uint8(v_env_3571_, sizeof(void*)*8);
if (v_isExporting_3575_ == 0)
{
v___y_3533_ = v___y_3553_;
v___y_3534_ = v___y_3554_;
v___y_3535_ = v___y_3555_;
v___y_3536_ = v___y_3556_;
v___y_3537_ = v___y_3557_;
v___y_3538_ = v___y_3558_;
v___y_3539_ = v___y_3559_;
v___y_3540_ = v___y_3560_;
v___y_3541_ = v___x_3574_;
v___y_3542_ = v___y_3562_;
v___y_3543_ = v___y_3561_;
v___y_3544_ = v_env_3571_;
v___y_3545_ = v___y_3563_;
v___y_3546_ = v___y_3565_;
v___y_3547_ = v___y_3564_;
v___y_3548_ = v___y_3567_;
v___y_3549_ = v___y_3566_;
v___y_3550_ = v___y_3568_;
goto v___jp_3532_;
}
else
{
if (v___y_3565_ == 0)
{
lean_dec_ref(v_env_3571_);
v___y_3510_ = v___y_3553_;
v___y_3511_ = v___y_3560_;
v___y_3512_ = v___y_3555_;
v___y_3513_ = v___y_3561_;
v___y_3514_ = v___y_3556_;
v___y_3515_ = v___y_3557_;
v___y_3516_ = v___y_3565_;
v___y_3517_ = v___y_3566_;
v___y_3518_ = v___y_3567_;
v___y_3519_ = v___y_3559_;
v_declName_3520_ = v___x_3574_;
v___y_3521_ = v___y_3563_;
v___y_3522_ = v___y_3564_;
v___y_3523_ = v___y_3568_;
v___y_3524_ = v___y_3558_;
v___y_3525_ = v___y_3554_;
v___y_3526_ = v___y_3562_;
goto v___jp_3509_;
}
else
{
v___y_3533_ = v___y_3553_;
v___y_3534_ = v___y_3554_;
v___y_3535_ = v___y_3555_;
v___y_3536_ = v___y_3556_;
v___y_3537_ = v___y_3557_;
v___y_3538_ = v___y_3558_;
v___y_3539_ = v___y_3559_;
v___y_3540_ = v___y_3560_;
v___y_3541_ = v___x_3574_;
v___y_3542_ = v___y_3562_;
v___y_3543_ = v___y_3561_;
v___y_3544_ = v_env_3571_;
v___y_3545_ = v___y_3563_;
v___y_3546_ = v___y_3565_;
v___y_3547_ = v___y_3564_;
v___y_3548_ = v___y_3567_;
v___y_3549_ = v___y_3566_;
v___y_3550_ = v___y_3568_;
goto v___jp_3532_;
}
}
}
}
v___jp_3576_:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v___y_3585_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = l_Lean_Syntax_getId(v___y_3584_);
if (lean_obj_tag(v_a_3592_) == 0)
{
lean_object* v___x_3594_; 
v___x_3594_ = lean_box(0);
v___y_3553_ = v___y_3577_;
v___y_3554_ = v___y_3589_;
v___y_3555_ = v___x_3593_;
v___y_3556_ = v___y_3579_;
v___y_3557_ = v___y_3580_;
v___y_3558_ = v___y_3588_;
v___y_3559_ = v___y_3584_;
v___y_3560_ = v_a_3592_;
v___y_3561_ = v___y_3578_;
v___y_3562_ = v___y_3590_;
v___y_3563_ = v___y_3585_;
v___y_3564_ = v___y_3586_;
v___y_3565_ = v___y_3581_;
v___y_3566_ = v___y_3583_;
v___y_3567_ = v___y_3582_;
v___y_3568_ = v___y_3587_;
v___y_3569_ = v___x_3594_;
goto v___jp_3552_;
}
else
{
lean_object* v_val_3595_; 
v_val_3595_ = lean_ctor_get(v_a_3592_, 0);
lean_inc(v_val_3595_);
v___y_3553_ = v___y_3577_;
v___y_3554_ = v___y_3589_;
v___y_3555_ = v___x_3593_;
v___y_3556_ = v___y_3579_;
v___y_3557_ = v___y_3580_;
v___y_3558_ = v___y_3588_;
v___y_3559_ = v___y_3584_;
v___y_3560_ = v_a_3592_;
v___y_3561_ = v___y_3578_;
v___y_3562_ = v___y_3590_;
v___y_3563_ = v___y_3585_;
v___y_3564_ = v___y_3586_;
v___y_3565_ = v___y_3581_;
v___y_3566_ = v___y_3583_;
v___y_3567_ = v___y_3582_;
v___y_3568_ = v___y_3587_;
v___y_3569_ = v_val_3595_;
goto v___jp_3552_;
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v___y_3584_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v_b_3314_);
v_a_3596_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3591_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3591_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
v___jp_3604_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; 
v___x_3618_ = l_Lean_Syntax_getArg(v___y_3609_, v___x_3329_);
v___x_3619_ = l_Lean_Syntax_getArg(v___x_3618_, v___x_3329_);
lean_dec(v___x_3618_);
v___x_3620_ = l_Lean_Syntax_isIdent(v___x_3619_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1);
v___x_3622_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___x_3619_, v___x_3621_, v___y_3613_, v___y_3617_, v___y_3612_, v___y_3614_, v___y_3608_, v___y_3610_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_dec_ref(v___x_3622_);
v___y_3577_ = v___y_3605_;
v___y_3578_ = v___y_3609_;
v___y_3579_ = v___y_3606_;
v___y_3580_ = v___y_3607_;
v___y_3581_ = v___y_3611_;
v___y_3582_ = v___y_3615_;
v___y_3583_ = v___y_3616_;
v___y_3584_ = v___x_3619_;
v___y_3585_ = v___y_3613_;
v___y_3586_ = v___y_3617_;
v___y_3587_ = v___y_3612_;
v___y_3588_ = v___y_3614_;
v___y_3589_ = v___y_3608_;
v___y_3590_ = v___y_3610_;
goto v___jp_3576_;
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v___x_3619_);
lean_dec(v___y_3609_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v_b_3314_);
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3622_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3622_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
v___y_3577_ = v___y_3605_;
v___y_3578_ = v___y_3609_;
v___y_3579_ = v___y_3606_;
v___y_3580_ = v___y_3607_;
v___y_3581_ = v___y_3611_;
v___y_3582_ = v___y_3615_;
v___y_3583_ = v___y_3616_;
v___y_3584_ = v___x_3619_;
v___y_3585_ = v___y_3613_;
v___y_3586_ = v___y_3617_;
v___y_3587_ = v___y_3612_;
v___y_3588_ = v___y_3614_;
v___y_3589_ = v___y_3608_;
v___y_3590_ = v___y_3610_;
goto v___jp_3576_;
}
}
v___jp_3631_:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v___x_3640_ = lean_unsigned_to_nat(2u);
v___x_3641_ = l_Lean_Syntax_getArg(v_a_3331_, v___x_3640_);
v___x_3642_ = l_Lean_Syntax_getArg(v___x_3641_, v___x_3329_);
lean_dec(v___x_3641_);
v___x_3643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3));
lean_inc(v___x_3642_);
v___x_3644_ = l_Lean_Syntax_isOfKind(v___x_3642_, v___x_3643_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5));
lean_inc(v___x_3642_);
v___x_3646_ = l_Lean_Syntax_isOfKind(v___x_3642_, v___x_3645_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7));
lean_inc(v___x_3642_);
v___x_3648_ = l_Lean_Syntax_isOfKind(v___x_3642_, v___x_3647_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; 
lean_dec(v___x_3642_);
lean_dec_ref(v_attrs_3633_);
lean_dec(v___y_3632_);
v___x_3649_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_dec_ref(v___x_3649_);
v_a_3323_ = v_b_3314_;
goto v___jp_3322_;
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec_ref(v_b_3314_);
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
else
{
v___y_3605_ = v___x_3644_;
v___y_3606_ = v_attrs_3633_;
v___y_3607_ = v___y_3632_;
v___y_3608_ = v___y_3638_;
v___y_3609_ = v___x_3642_;
v___y_3610_ = v___y_3639_;
v___y_3611_ = v___x_3644_;
v___y_3612_ = v___y_3636_;
v___y_3613_ = v___y_3634_;
v___y_3614_ = v___y_3637_;
v___y_3615_ = v___x_3646_;
v___y_3616_ = v___x_3640_;
v___y_3617_ = v___y_3635_;
goto v___jp_3604_;
}
}
else
{
v___y_3605_ = v___x_3644_;
v___y_3606_ = v_attrs_3633_;
v___y_3607_ = v___y_3632_;
v___y_3608_ = v___y_3638_;
v___y_3609_ = v___x_3642_;
v___y_3610_ = v___y_3639_;
v___y_3611_ = v___x_3644_;
v___y_3612_ = v___y_3636_;
v___y_3613_ = v___y_3634_;
v___y_3614_ = v___y_3637_;
v___y_3615_ = v___x_3646_;
v___y_3616_ = v___x_3640_;
v___y_3617_ = v___y_3635_;
goto v___jp_3604_;
}
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_dec_ref(v_attrs_3633_);
lean_dec(v___y_3632_);
v___x_3658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9);
v___x_3659_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___x_3642_, v___x_3658_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___x_3642_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_dec_ref(v___x_3659_);
v_a_3323_ = v_b_3314_;
goto v___jp_3322_;
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec_ref(v_b_3314_);
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
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
}
v___jp_3668_:
{
lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3670_ = l_Lean_Syntax_getArg(v_a_3331_, v___x_3330_);
v___x_3671_ = l_Lean_Syntax_isNone(v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = l_Lean_Syntax_getArg(v___x_3670_, v___x_3329_);
lean_dec(v___x_3670_);
v___x_3673_ = l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(v___x_3672_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___x_3672_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v___y_3632_ = v___y_3669_;
v_attrs_3633_ = v_a_3674_;
v___y_3634_ = v___y_3315_;
v___y_3635_ = v___y_3316_;
v___y_3636_ = v___y_3317_;
v___y_3637_ = v___y_3318_;
v___y_3638_ = v___y_3319_;
v___y_3639_ = v___y_3320_;
goto v___jp_3631_;
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec(v___y_3669_);
lean_dec_ref(v_b_3314_);
v_a_3675_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3673_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3673_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v___x_3683_; 
lean_dec(v___x_3670_);
v___x_3683_ = ((lean_object*)(l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___closed__0));
v___y_3632_ = v___y_3669_;
v_attrs_3633_ = v___x_3683_;
v___y_3634_ = v___y_3315_;
v___y_3635_ = v___y_3316_;
v___y_3636_ = v___y_3317_;
v___y_3637_ = v___y_3318_;
v___y_3638_ = v___y_3319_;
v___y_3639_ = v___y_3320_;
goto v___jp_3631_;
}
}
}
v___jp_3322_:
{
size_t v___x_3324_; size_t v___x_3325_; 
v___x_3324_ = ((size_t)1ULL);
v___x_3325_ = lean_usize_add(v_i_3313_, v___x_3324_);
v_i_3313_ = v___x_3325_;
v_b_3314_ = v_a_3323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___boxed(lean_object* v___x_3697_, lean_object* v_as_3698_, lean_object* v_sz_3699_, lean_object* v_i_3700_, lean_object* v_b_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v___x_57667__boxed_3709_; size_t v_sz_boxed_3710_; size_t v_i_boxed_3711_; lean_object* v_res_3712_; 
v___x_57667__boxed_3709_ = lean_unbox(v___x_3697_);
v_sz_boxed_3710_ = lean_unbox_usize(v_sz_3699_);
lean_dec(v_sz_3699_);
v_i_boxed_3711_ = lean_unbox_usize(v_i_3700_);
lean_dec(v_i_3700_);
v_res_3712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(v___x_57667__boxed_3709_, v_as_3698_, v_sz_boxed_3710_, v_i_boxed_3711_, v_b_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec_ref(v_as_3698_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(lean_object* v_letRec_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v_options_3723_; lean_object* v___x_3724_; lean_object* v_decls_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; size_t v_sz_3732_; size_t v___x_3733_; lean_object* v___x_3734_; 
v_options_3723_ = lean_ctor_get(v_a_3720_, 2);
v___x_3724_ = lean_unsigned_to_nat(0u);
v_decls_3725_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___closed__0));
v___x_3726_ = l_Lean_doc_verso;
v___x_3727_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_options_3723_, v___x_3726_);
v___x_3728_ = lean_unsigned_to_nat(1u);
v___x_3729_ = l_Lean_Syntax_getArg(v_letRec_3715_, v___x_3728_);
v___x_3730_ = l_Lean_Syntax_getArg(v___x_3729_, v___x_3724_);
lean_dec(v___x_3729_);
v___x_3731_ = l_Lean_Syntax_getSepArgs(v___x_3730_);
lean_dec(v___x_3730_);
v_sz_3732_ = lean_array_size(v___x_3731_);
v___x_3733_ = ((size_t)0ULL);
v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(v___x_3727_, v___x_3731_, v_sz_3732_, v___x_3733_, v_decls_3725_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_);
lean_dec_ref(v___x_3731_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3745_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3745_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3745_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3743_; 
v___x_3739_ = lean_unsigned_to_nat(3u);
v___x_3740_ = l_Lean_Syntax_getArg(v_letRec_3715_, v___x_3739_);
v___x_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3741_, 0, v_a_3735_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3741_);
v___x_3743_ = v___x_3737_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
v_a_3746_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3734_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3734_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___boxed(lean_object* v_letRec_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(v_letRec_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
lean_dec(v_letRec_3754_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5(lean_object* v_stx_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_stx_3763_, v___y_3768_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___boxed(lean_object* v_stx_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5(v_stx_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v_stx_3772_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6(lean_object* v_declName_3781_, lean_object* v_declRanges_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_3781_, v_declRanges_3782_, v___y_3786_, v___y_3788_);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___boxed(lean_object* v_declName_3791_, lean_object* v_declRanges_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6(v_declName_3791_, v_declRanges_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(lean_object* v_00_u03b1_3801_, lean_object* v_x_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_x_3802_, v___y_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___boxed(lean_object* v_00_u03b1_3806_, lean_object* v_x_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(v_00_u03b1_3806_, v_x_3807_, v___y_3808_, v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec_ref(v_x_3807_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(lean_object* v_00_u03b1_3811_, lean_object* v_ref_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(v_ref_3812_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___boxed(lean_object* v_00_u03b1_3821_, lean_object* v_ref_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(v_00_u03b1_3821_, v_ref_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4(lean_object* v_00_u03b1_3831_, lean_object* v_x_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v_x_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___boxed(lean_object* v_00_u03b1_3841_, lean_object* v_x_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4(v_00_u03b1_3841_, v_x_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5(lean_object* v_00_u03b1_3851_, lean_object* v_msg_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v_msg_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___boxed(lean_object* v_00_u03b1_3861_, lean_object* v_msg_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5(v_00_u03b1_3861_, v_msg_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6(lean_object* v_t_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v_t_3871_, v___y_3877_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___boxed(lean_object* v_t_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6(v_t_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8(lean_object* v_env_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3889_, v___y_3893_, v___y_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___boxed(lean_object* v_env_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8(v_env_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3(lean_object* v_00_u03b1_3907_, lean_object* v_env_3908_, lean_object* v_x_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3908_, v_x_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3918_, lean_object* v_env_3919_, lean_object* v_x_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3(v_00_u03b1_3918_, v_env_3919_, v_x_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(lean_object* v_cls_3929_, lean_object* v_msg_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v___x_3938_; 
v___x_3938_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_3929_, v_msg_3930_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___boxed(lean_object* v_cls_3939_, lean_object* v_msg_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(v_cls_3939_, v_msg_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(lean_object* v_as_3949_, lean_object* v_as_x27_3950_, lean_object* v_b_3951_, lean_object* v_a_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(v_as_x27_3950_, v_b_3951_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___boxed(lean_object* v_as_3961_, lean_object* v_as_x27_3962_, lean_object* v_b_3963_, lean_object* v_a_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(v_as_3961_, v_as_x27_3962_, v_b_3963_, v_a_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v_as_x27_3962_);
lean_dec(v_as_3961_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(lean_object* v_msgData_3973_, lean_object* v_macroStack_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg(v_msgData_3973_, v_macroStack_3974_, v___y_3979_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___boxed(lean_object* v_msgData_3983_, lean_object* v_macroStack_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(v_msgData_3983_, v_macroStack_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19(lean_object* v_00_u03b2_3993_, lean_object* v_m_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(v_m_3994_, v_a_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___boxed(lean_object* v_00_u03b2_3997_, lean_object* v_m_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19(v_00_u03b2_3997_, v_m_3998_, v_a_3999_);
lean_dec(v_a_3999_);
lean_dec_ref(v_m_3998_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17(lean_object* v_00_u03b1_4001_, lean_object* v_constName_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(v_constName_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___boxed(lean_object* v_00_u03b1_4011_, lean_object* v_constName_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17(v_00_u03b1_4011_, v_constName_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
return v_res_4020_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26(lean_object* v_00_u03b2_4021_, lean_object* v_x_4022_, lean_object* v_x_4023_){
_start:
{
uint8_t v___x_4024_; 
v___x_4024_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(v_x_4022_, v_x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___boxed(lean_object* v_00_u03b2_4025_, lean_object* v_x_4026_, lean_object* v_x_4027_){
_start:
{
uint8_t v_res_4028_; lean_object* v_r_4029_; 
v_res_4028_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26(v_00_u03b2_4025_, v_x_4026_, v_x_4027_);
lean_dec_ref(v_x_4027_);
lean_dec_ref(v_x_4026_);
v_r_4029_ = lean_box(v_res_4028_);
return v_r_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29(lean_object* v_00_u03b2_4030_, lean_object* v_a_4031_, lean_object* v_x_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(v_a_4031_, v_x_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___boxed(lean_object* v_00_u03b2_4034_, lean_object* v_a_4035_, lean_object* v_x_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29(v_00_u03b2_4034_, v_a_4035_, v_x_4036_);
lean_dec(v_x_4036_);
lean_dec(v_a_4035_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39(lean_object* v_00_u03b1_4038_, lean_object* v_x_4039_, uint8_t v_isExporting_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(v_x_4039_, v_isExporting_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___boxed(lean_object* v_00_u03b1_4049_, lean_object* v_x_4050_, lean_object* v_isExporting_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
uint8_t v_isExporting_boxed_4059_; lean_object* v_res_4060_; 
v_isExporting_boxed_4059_ = lean_unbox(v_isExporting_4051_);
v_res_4060_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39(v_00_u03b1_4049_, v_x_4050_, v_isExporting_boxed_4059_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36(lean_object* v_00_u03b1_4061_, lean_object* v_x_4062_, uint8_t v_when_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(v_x_4062_, v_when_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___boxed(lean_object* v_00_u03b1_4072_, lean_object* v_x_4073_, lean_object* v_when_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
uint8_t v_when_boxed_4082_; lean_object* v_res_4083_; 
v_when_boxed_4082_ = lean_unbox(v_when_4074_);
v_res_4083_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36(v_00_u03b1_4072_, v_x_4073_, v_when_boxed_4082_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28(lean_object* v_00_u03b1_4084_, lean_object* v_ref_4085_, lean_object* v_constName_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v___x_4094_; 
v___x_4094_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(v_ref_4085_, v_constName_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___boxed(lean_object* v_00_u03b1_4095_, lean_object* v_ref_4096_, lean_object* v_constName_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28(v_00_u03b1_4095_, v_ref_4096_, v_constName_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v_ref_4096_);
return v_res_4105_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32(lean_object* v_00_u03b2_4106_, lean_object* v_x_4107_, size_t v_x_4108_, lean_object* v_x_4109_){
_start:
{
uint8_t v___x_4110_; 
v___x_4110_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(v_x_4107_, v_x_4108_, v_x_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4111_, lean_object* v_x_4112_, lean_object* v_x_4113_, lean_object* v_x_4114_){
_start:
{
size_t v_x_58861__boxed_4115_; uint8_t v_res_4116_; lean_object* v_r_4117_; 
v_x_58861__boxed_4115_ = lean_unbox_usize(v_x_4113_);
lean_dec(v_x_4113_);
v_res_4116_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32(v_00_u03b2_4111_, v_x_4112_, v_x_58861__boxed_4115_, v_x_4114_);
lean_dec_ref(v_x_4114_);
lean_dec_ref(v_x_4112_);
v_r_4117_ = lean_box(v_res_4116_);
return v_r_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42(lean_object* v_ref_4118_, lean_object* v_msgData_4119_, uint8_t v_severity_4120_, uint8_t v_isSilent_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(v_ref_4118_, v_msgData_4119_, v_severity_4120_, v_isSilent_4121_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___boxed(lean_object* v_ref_4130_, lean_object* v_msgData_4131_, lean_object* v_severity_4132_, lean_object* v_isSilent_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
uint8_t v_severity_boxed_4141_; uint8_t v_isSilent_boxed_4142_; lean_object* v_res_4143_; 
v_severity_boxed_4141_ = lean_unbox(v_severity_4132_);
v_isSilent_boxed_4142_ = lean_unbox(v_isSilent_4133_);
v_res_4143_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42(v_ref_4130_, v_msgData_4131_, v_severity_boxed_4141_, v_isSilent_boxed_4142_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v_ref_4130_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37(lean_object* v_00_u03b1_4144_, lean_object* v_ref_4145_, lean_object* v_msg_4146_, lean_object* v_declHint_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v___x_4155_; 
v___x_4155_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(v_ref_4145_, v_msg_4146_, v_declHint_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___boxed(lean_object* v_00_u03b1_4156_, lean_object* v_ref_4157_, lean_object* v_msg_4158_, lean_object* v_declHint_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37(v_00_u03b1_4156_, v_ref_4157_, v_msg_4158_, v_declHint_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v_ref_4157_);
return v_res_4167_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40(lean_object* v_00_u03b2_4168_, lean_object* v_keys_4169_, lean_object* v_vals_4170_, lean_object* v_heq_4171_, lean_object* v_i_4172_, lean_object* v_k_4173_){
_start:
{
uint8_t v___x_4174_; 
v___x_4174_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(v_keys_4169_, v_i_4172_, v_k_4173_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___boxed(lean_object* v_00_u03b2_4175_, lean_object* v_keys_4176_, lean_object* v_vals_4177_, lean_object* v_heq_4178_, lean_object* v_i_4179_, lean_object* v_k_4180_){
_start:
{
uint8_t v_res_4181_; lean_object* v_r_4182_; 
v_res_4181_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40(v_00_u03b2_4175_, v_keys_4176_, v_vals_4177_, v_heq_4178_, v_i_4179_, v_k_4180_);
lean_dec_ref(v_k_4180_);
lean_dec_ref(v_vals_4177_);
lean_dec_ref(v_keys_4176_);
v_r_4182_ = lean_box(v_res_4181_);
return v_r_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48(lean_object* v_msg_4183_, lean_object* v_declHint_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(v_msg_4183_, v_declHint_4184_, v___y_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___boxed(lean_object* v_msg_4193_, lean_object* v_declHint_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48(v_msg_4193_, v_declHint_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0(lean_object* v_k_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v_b_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; 
lean_inc(v___y_4210_);
lean_inc_ref(v___y_4209_);
lean_inc(v___y_4208_);
lean_inc_ref(v___y_4207_);
lean_inc(v___y_4205_);
lean_inc_ref(v___y_4204_);
v___x_4212_ = lean_apply_8(v_k_4203_, v_b_4206_, v___y_4204_, v___y_4205_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, lean_box(0));
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v_b_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0(v_k_4213_, v___y_4214_, v___y_4215_, v_b_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(lean_object* v_shortDeclName_4223_, lean_object* v_type_4224_, lean_object* v_declName_4225_, lean_object* v_k_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___f_4234_; lean_object* v___x_4235_; 
lean_inc(v___y_4228_);
lean_inc_ref(v___y_4227_);
v___f_4234_ = lean_alloc_closure((void*)(l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4234_, 0, v_k_4226_);
lean_closure_set(v___f_4234_, 1, v___y_4227_);
lean_closure_set(v___f_4234_, 2, v___y_4228_);
v___x_4235_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withAuxDeclImp(lean_box(0), v_shortDeclName_4223_, v_type_4224_, v_declName_4225_, v___f_4234_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
if (lean_obj_tag(v___x_4235_) == 0)
{
return v___x_4235_;
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4235_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4235_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___boxed(lean_object* v_shortDeclName_4244_, lean_object* v_type_4245_, lean_object* v_declName_4246_, lean_object* v_k_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4244_, v_type_4245_, v_declName_4246_, v_k_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec(v___y_4249_);
lean_dec_ref(v___y_4248_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0(lean_object* v_00_u03b1_4256_, lean_object* v_shortDeclName_4257_, lean_object* v_type_4258_, lean_object* v_declName_4259_, lean_object* v_k_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4257_, v_type_4258_, v_declName_4259_, v_k_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___boxed(lean_object* v_00_u03b1_4269_, lean_object* v_shortDeclName_4270_, lean_object* v_type_4271_, lean_object* v_declName_4272_, lean_object* v_k_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0(v_00_u03b1_4269_, v_shortDeclName_4270_, v_type_4271_, v_declName_4272_, v_k_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0___boxed(lean_object* v_i_4282_, lean_object* v_fvars_4283_, lean_object* v_views_4284_, lean_object* v_k_4285_, lean_object* v_fvar_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0(v_i_4282_, v_fvars_4283_, v_views_4284_, v_k_4285_, v_fvar_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v_i_4282_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(lean_object* v_views_4295_, lean_object* v_k_4296_, lean_object* v_i_4297_, lean_object* v_fvars_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4306_ = lean_array_get_size(v_views_4295_);
v___x_4307_ = lean_nat_dec_lt(v_i_4297_, v___x_4306_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4308_; 
lean_dec(v_i_4297_);
lean_dec_ref(v_views_4295_);
lean_inc(v_a_4304_);
lean_inc_ref(v_a_4303_);
lean_inc(v_a_4302_);
lean_inc_ref(v_a_4301_);
lean_inc(v_a_4300_);
lean_inc_ref(v_a_4299_);
v___x_4308_ = lean_apply_8(v_k_4296_, v_fvars_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, lean_box(0));
return v___x_4308_;
}
else
{
lean_object* v_view_4309_; lean_object* v_shortDeclName_4310_; lean_object* v_declName_4311_; lean_object* v_type_4312_; lean_object* v___f_4313_; lean_object* v___x_4314_; 
v_view_4309_ = lean_array_fget_borrowed(v_views_4295_, v_i_4297_);
v_shortDeclName_4310_ = lean_ctor_get(v_view_4309_, 2);
lean_inc(v_shortDeclName_4310_);
v_declName_4311_ = lean_ctor_get(v_view_4309_, 3);
lean_inc(v_declName_4311_);
v_type_4312_ = lean_ctor_get(v_view_4309_, 7);
lean_inc_ref(v_type_4312_);
v___f_4313_ = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4313_, 0, v_i_4297_);
lean_closure_set(v___f_4313_, 1, v_fvars_4298_);
lean_closure_set(v___f_4313_, 2, v_views_4295_);
lean_closure_set(v___f_4313_, 3, v_k_4296_);
v___x_4314_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4310_, v_type_4312_, v_declName_4311_, v___f_4313_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
return v___x_4314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0(lean_object* v_i_4315_, lean_object* v_fvars_4316_, lean_object* v_views_4317_, lean_object* v_k_4318_, lean_object* v_fvar_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4327_ = lean_unsigned_to_nat(1u);
v___x_4328_ = lean_nat_add(v_i_4315_, v___x_4327_);
v___x_4329_ = lean_array_push(v_fvars_4316_, v_fvar_4319_);
v___x_4330_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4317_, v_k_4318_, v___x_4328_, v___x_4329_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___boxed(lean_object* v_views_4331_, lean_object* v_k_4332_, lean_object* v_i_4333_, lean_object* v_fvars_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4331_, v_k_4332_, v_i_4333_, v_fvars_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_);
lean_dec(v_a_4340_);
lean_dec_ref(v_a_4339_);
lean_dec(v_a_4338_);
lean_dec_ref(v_a_4337_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(lean_object* v_00_u03b1_4343_, lean_object* v_views_4344_, lean_object* v_k_4345_, lean_object* v_i_4346_, lean_object* v_fvars_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4344_, v_k_4345_, v_i_4346_, v_fvars_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___boxed(lean_object* v_00_u03b1_4356_, lean_object* v_views_4357_, lean_object* v_k_4358_, lean_object* v_i_4359_, lean_object* v_fvars_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(v_00_u03b1_4356_, v_views_4357_, v_k_4358_, v_i_4359_, v_fvars_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
lean_dec(v_a_4364_);
lean_dec_ref(v_a_4363_);
lean_dec(v_a_4362_);
lean_dec_ref(v_a_4361_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(lean_object* v_views_4371_, lean_object* v_k_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4380_ = lean_unsigned_to_nat(0u);
v___x_4381_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___closed__0));
v___x_4382_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4371_, v_k_4372_, v___x_4380_, v___x_4381_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___boxed(lean_object* v_views_4383_, lean_object* v_k_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_views_4383_, v_k_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
return v_res_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(lean_object* v_00_u03b1_4393_, lean_object* v_views_4394_, lean_object* v_k_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_views_4394_, v_k_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___boxed(lean_object* v_00_u03b1_4404_, lean_object* v_views_4405_, lean_object* v_k_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(v_00_u03b1_4404_, v_views_4405_, v_k_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_);
lean_dec(v_a_4412_);
lean_dec_ref(v_a_4411_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
lean_dec(v_a_4408_);
lean_dec_ref(v_a_4407_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0(lean_object* v_k_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v_b_4418_, lean_object* v_c_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v___x_4425_; 
lean_inc(v___y_4423_);
lean_inc_ref(v___y_4422_);
lean_inc(v___y_4421_);
lean_inc_ref(v___y_4420_);
lean_inc(v___y_4417_);
lean_inc_ref(v___y_4416_);
v___x_4425_ = lean_apply_9(v_k_4415_, v_b_4418_, v_c_4419_, v___y_4416_, v___y_4417_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, lean_box(0));
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0___boxed(lean_object* v_k_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v_b_4429_, lean_object* v_c_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0(v_k_4426_, v___y_4427_, v___y_4428_, v_b_4429_, v_c_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(lean_object* v_type_4437_, lean_object* v_maxFVars_x3f_4438_, lean_object* v_k_4439_, uint8_t v_cleanupAnnotations_4440_, uint8_t v_whnfType_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v___f_4449_; lean_object* v___x_4450_; 
lean_inc(v___y_4443_);
lean_inc_ref(v___y_4442_);
v___f_4449_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4449_, 0, v_k_4439_);
lean_closure_set(v___f_4449_, 1, v___y_4442_);
lean_closure_set(v___f_4449_, 2, v___y_4443_);
v___x_4450_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4437_, v_maxFVars_x3f_4438_, v___f_4449_, v_cleanupAnnotations_4440_, v_whnfType_4441_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
if (lean_obj_tag(v___x_4450_) == 0)
{
return v___x_4450_;
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4450_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4450_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___boxed(lean_object* v_type_4459_, lean_object* v_maxFVars_x3f_4460_, lean_object* v_k_4461_, lean_object* v_cleanupAnnotations_4462_, lean_object* v_whnfType_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4471_; uint8_t v_whnfType_boxed_4472_; lean_object* v_res_4473_; 
v_cleanupAnnotations_boxed_4471_ = lean_unbox(v_cleanupAnnotations_4462_);
v_whnfType_boxed_4472_ = lean_unbox(v_whnfType_4463_);
v_res_4473_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4459_, v_maxFVars_x3f_4460_, v_k_4461_, v_cleanupAnnotations_boxed_4471_, v_whnfType_boxed_4472_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1(lean_object* v_00_u03b1_4474_, lean_object* v_type_4475_, lean_object* v_maxFVars_x3f_4476_, lean_object* v_k_4477_, uint8_t v_cleanupAnnotations_4478_, uint8_t v_whnfType_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v___x_4487_; 
v___x_4487_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4475_, v_maxFVars_x3f_4476_, v_k_4477_, v_cleanupAnnotations_4478_, v_whnfType_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___boxed(lean_object* v_00_u03b1_4488_, lean_object* v_type_4489_, lean_object* v_maxFVars_x3f_4490_, lean_object* v_k_4491_, lean_object* v_cleanupAnnotations_4492_, lean_object* v_whnfType_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4501_; uint8_t v_whnfType_boxed_4502_; lean_object* v_res_4503_; 
v_cleanupAnnotations_boxed_4501_ = lean_unbox(v_cleanupAnnotations_4492_);
v_whnfType_boxed_4502_ = lean_unbox(v_whnfType_4493_);
v_res_4503_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1(v_00_u03b1_4488_, v_type_4489_, v_maxFVars_x3f_4490_, v_k_4491_, v_cleanupAnnotations_boxed_4501_, v_whnfType_boxed_4502_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0(lean_object* v_valStx_4504_, lean_object* v_x_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4513_, 0, v_x_4505_);
v___x_4514_ = l_Lean_Elab_Term_mkBodyInfo(v_valStx_4504_, v___x_4513_);
v___x_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4515_, 0, v___x_4514_);
v___x_4516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0___boxed(lean_object* v_valStx_4517_, lean_object* v_x_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0(v_valStx_4517_, v_x_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(lean_object* v_upperBound_4527_, lean_object* v___x_4528_, lean_object* v_xs_4529_, lean_object* v_a_4530_, lean_object* v_b_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
uint8_t v___x_4539_; 
v___x_4539_ = lean_nat_dec_lt(v_a_4530_, v_upperBound_4527_);
if (v___x_4539_ == 0)
{
lean_object* v___x_4540_; 
lean_dec(v_a_4530_);
v___x_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4540_, 0, v_b_4531_);
return v___x_4540_;
}
else
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4541_ = l_Lean_instInhabitedExpr;
v___x_4542_ = lean_array_fget_borrowed(v___x_4528_, v_a_4530_);
v___x_4543_ = lean_array_get_borrowed(v___x_4541_, v_xs_4529_, v_a_4530_);
lean_inc(v___x_4543_);
lean_inc(v___x_4542_);
v___x_4544_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_4542_, v___x_4543_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; 
lean_dec_ref(v___x_4544_);
v___x_4545_ = lean_box(0);
v___x_4546_ = lean_unsigned_to_nat(1u);
v___x_4547_ = lean_nat_add(v_a_4530_, v___x_4546_);
lean_dec(v_a_4530_);
v_a_4530_ = v___x_4547_;
v_b_4531_ = v___x_4545_;
goto _start;
}
else
{
lean_dec(v_a_4530_);
return v___x_4544_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg___boxed(lean_object* v_upperBound_4549_, lean_object* v___x_4550_, lean_object* v_xs_4551_, lean_object* v_a_4552_, lean_object* v_b_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v_upperBound_4549_, v___x_4550_, v_xs_4551_, v_a_4552_, v_b_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec_ref(v_xs_4551_);
lean_dec_ref(v___x_4550_);
lean_dec(v_upperBound_4549_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1(lean_object* v_valStx_4562_, lean_object* v___x_4563_, uint8_t v___x_4564_, lean_object* v___x_4565_, lean_object* v_xs_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
lean_object* v___x_4574_; 
v___x_4574_ = l_Lean_Elab_Term_elabTermEnsuringType(v_valStx_4562_, v___x_4563_, v___x_4564_, v___x_4564_, v___x_4565_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; uint8_t v___x_4576_; uint8_t v___x_4577_; lean_object* v___x_4578_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref(v___x_4574_);
v___x_4576_ = 0;
v___x_4577_ = 1;
v___x_4578_ = l_Lean_Meta_mkLambdaFVars(v_xs_4566_, v_a_4575_, v___x_4576_, v___x_4564_, v___x_4576_, v___x_4564_, v___x_4577_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
return v___x_4578_;
}
else
{
return v___x_4574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1___boxed(lean_object* v_valStx_4579_, lean_object* v___x_4580_, lean_object* v___x_4581_, lean_object* v___x_4582_, lean_object* v_xs_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
uint8_t v___x_3132__boxed_4591_; lean_object* v_res_4592_; 
v___x_3132__boxed_4591_ = lean_unbox(v___x_4581_);
v_res_4592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1(v_valStx_4579_, v___x_4580_, v___x_3132__boxed_4591_, v___x_4582_, v_xs_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec(v___y_4587_);
lean_dec_ref(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
lean_dec_ref(v_xs_4583_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2(lean_object* v___x_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4593_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2___boxed(lean_object* v___x_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2(v___x_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3(lean_object* v___x_4611_, lean_object* v_binderIds_4612_, lean_object* v_valStx_4613_, uint8_t v___x_4614_, lean_object* v___f_4615_, lean_object* v_declName_4616_, lean_object* v_xs_4617_, lean_object* v_type_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4626_ = lean_unsigned_to_nat(0u);
v___x_4627_ = lean_box(0);
v___x_4628_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v___x_4611_, v_binderIds_4612_, v_xs_4617_, v___x_4626_, v___x_4627_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___f_4632_; lean_object* v___x_4633_; lean_object* v___f_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
lean_dec_ref(v___x_4628_);
v___x_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4629_, 0, v_type_4618_);
v___x_4630_ = lean_box(0);
v___x_4631_ = lean_box(v___x_4614_);
lean_inc_n(v_valStx_4613_, 2);
v___f_4632_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4632_, 0, v_valStx_4613_);
lean_closure_set(v___f_4632_, 1, v___x_4629_);
lean_closure_set(v___f_4632_, 2, v___x_4631_);
lean_closure_set(v___f_4632_, 3, v___x_4630_);
lean_closure_set(v___f_4632_, 4, v_xs_4617_);
v___x_4633_ = l_Lean_Elab_Term_mkBodyInfo(v_valStx_4613_, v___x_4630_);
v___f_4634_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2___boxed), 8, 1);
lean_closure_set(v___f_4634_, 0, v___x_4633_);
v___x_4635_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withInfoContext_x27___boxed), 11, 4);
lean_closure_set(v___x_4635_, 0, v_valStx_4613_);
lean_closure_set(v___x_4635_, 1, v___f_4632_);
lean_closure_set(v___x_4635_, 2, v___f_4615_);
lean_closure_set(v___x_4635_, 3, v___f_4634_);
v___x_4636_ = l_Lean_Elab_Term_withDeclName___redArg(v_declName_4616_, v___x_4635_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
return v___x_4636_;
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_dec_ref(v_type_4618_);
lean_dec_ref(v_xs_4617_);
lean_dec(v_declName_4616_);
lean_dec_ref(v___f_4615_);
lean_dec(v_valStx_4613_);
v_a_4637_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4628_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4628_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3___boxed(lean_object* v___x_4645_, lean_object* v_binderIds_4646_, lean_object* v_valStx_4647_, lean_object* v___x_4648_, lean_object* v___f_4649_, lean_object* v_declName_4650_, lean_object* v_xs_4651_, lean_object* v_type_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
uint8_t v___x_3199__boxed_4660_; lean_object* v_res_4661_; 
v___x_3199__boxed_4660_ = lean_unbox(v___x_4648_);
v_res_4661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3(v___x_4645_, v_binderIds_4646_, v_valStx_4647_, v___x_3199__boxed_4660_, v___f_4649_, v_declName_4650_, v_xs_4651_, v_type_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec_ref(v_binderIds_4646_);
lean_dec(v___x_4645_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(size_t v_sz_4662_, size_t v_i_4663_, lean_object* v_bs_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
uint8_t v___x_4672_; 
v___x_4672_ = lean_usize_dec_lt(v_i_4663_, v_sz_4662_);
if (v___x_4672_ == 0)
{
lean_object* v___x_4673_; 
v___x_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4673_, 0, v_bs_4664_);
return v___x_4673_;
}
else
{
lean_object* v_v_4674_; lean_object* v_declName_4675_; lean_object* v_binderIds_4676_; lean_object* v_type_4677_; lean_object* v_valStx_4678_; lean_object* v___f_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___f_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; lean_object* v___x_4685_; 
v_v_4674_ = lean_array_uget_borrowed(v_bs_4664_, v_i_4663_);
v_declName_4675_ = lean_ctor_get(v_v_4674_, 3);
v_binderIds_4676_ = lean_ctor_get(v_v_4674_, 5);
v_type_4677_ = lean_ctor_get(v_v_4674_, 7);
v_valStx_4678_ = lean_ctor_get(v_v_4674_, 9);
lean_inc_n(v_valStx_4678_, 2);
v___f_4679_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4679_, 0, v_valStx_4678_);
v___x_4680_ = lean_array_get_size(v_binderIds_4676_);
v___x_4681_ = lean_box(v___x_4672_);
lean_inc(v_declName_4675_);
lean_inc_ref(v_binderIds_4676_);
v___f_4682_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3___boxed), 15, 6);
lean_closure_set(v___f_4682_, 0, v___x_4680_);
lean_closure_set(v___f_4682_, 1, v_binderIds_4676_);
lean_closure_set(v___f_4682_, 2, v_valStx_4678_);
lean_closure_set(v___f_4682_, 3, v___x_4681_);
lean_closure_set(v___f_4682_, 4, v___f_4679_);
lean_closure_set(v___f_4682_, 5, v_declName_4675_);
v___x_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4680_);
v___x_4684_ = 0;
lean_inc_ref(v_type_4677_);
v___x_4685_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4677_, v___x_4683_, v___f_4682_, v___x_4672_, v___x_4684_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
if (lean_obj_tag(v___x_4685_) == 0)
{
lean_object* v_a_4686_; lean_object* v___x_4687_; lean_object* v_bs_x27_4688_; size_t v___x_4689_; size_t v___x_4690_; lean_object* v___x_4691_; 
v_a_4686_ = lean_ctor_get(v___x_4685_, 0);
lean_inc(v_a_4686_);
lean_dec_ref(v___x_4685_);
v___x_4687_ = lean_unsigned_to_nat(0u);
v_bs_x27_4688_ = lean_array_uset(v_bs_4664_, v_i_4663_, v___x_4687_);
v___x_4689_ = ((size_t)1ULL);
v___x_4690_ = lean_usize_add(v_i_4663_, v___x_4689_);
v___x_4691_ = lean_array_uset(v_bs_x27_4688_, v_i_4663_, v_a_4686_);
v_i_4663_ = v___x_4690_;
v_bs_4664_ = v___x_4691_;
goto _start;
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4700_; 
lean_dec_ref(v_bs_4664_);
v_a_4693_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4695_ = v___x_4685_;
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4685_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___boxed(lean_object* v_sz_4701_, lean_object* v_i_4702_, lean_object* v_bs_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
size_t v_sz_boxed_4711_; size_t v_i_boxed_4712_; lean_object* v_res_4713_; 
v_sz_boxed_4711_ = lean_unbox_usize(v_sz_4701_);
lean_dec(v_sz_4701_);
v_i_boxed_4712_ = lean_unbox_usize(v_i_4702_);
lean_dec(v_i_4702_);
v_res_4713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(v_sz_boxed_4711_, v_i_boxed_4712_, v_bs_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(lean_object* v_view_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v_decls_4722_; size_t v_sz_4723_; size_t v___x_4724_; lean_object* v___x_4725_; 
v_decls_4722_ = lean_ctor_get(v_view_4714_, 0);
lean_inc_ref(v_decls_4722_);
lean_dec_ref(v_view_4714_);
v_sz_4723_ = lean_array_size(v_decls_4722_);
v___x_4724_ = ((size_t)0ULL);
v___x_4725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(v_sz_4723_, v___x_4724_, v_decls_4722_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___boxed(lean_object* v_view_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_){
_start:
{
lean_object* v_res_4734_; 
v_res_4734_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(v_view_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
lean_dec(v_a_4728_);
lean_dec_ref(v_a_4727_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0(lean_object* v_upperBound_4735_, lean_object* v___x_4736_, lean_object* v_xs_4737_, lean_object* v_inst_4738_, lean_object* v_R_4739_, lean_object* v_a_4740_, lean_object* v_b_4741_, lean_object* v_c_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v___x_4750_; 
v___x_4750_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v_upperBound_4735_, v___x_4736_, v_xs_4737_, v_a_4740_, v_b_4741_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___boxed(lean_object* v_upperBound_4751_, lean_object* v___x_4752_, lean_object* v_xs_4753_, lean_object* v_inst_4754_, lean_object* v_R_4755_, lean_object* v_a_4756_, lean_object* v_b_4757_, lean_object* v_c_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0(v_upperBound_4751_, v___x_4752_, v_xs_4753_, v_inst_4754_, v_R_4755_, v_a_4756_, v_b_4757_, v_c_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec_ref(v_xs_4753_);
lean_dec_ref(v___x_4752_);
lean_dec(v_upperBound_4751_);
return v_res_4766_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(lean_object* v_a_4767_, lean_object* v_x_4768_){
_start:
{
if (lean_obj_tag(v_x_4768_) == 0)
{
uint8_t v___x_4769_; 
v___x_4769_ = 0;
return v___x_4769_;
}
else
{
lean_object* v_head_4770_; lean_object* v_tail_4771_; lean_object* v_declName_4772_; lean_object* v_declName_4773_; uint8_t v___x_4774_; 
v_head_4770_ = lean_ctor_get(v_x_4768_, 0);
v_tail_4771_ = lean_ctor_get(v_x_4768_, 1);
v_declName_4772_ = lean_ctor_get(v_head_4770_, 4);
v_declName_4773_ = lean_ctor_get(v_a_4767_, 3);
v___x_4774_ = lean_name_eq(v_declName_4772_, v_declName_4773_);
if (v___x_4774_ == 0)
{
v_x_4768_ = v_tail_4771_;
goto _start;
}
else
{
return v___x_4774_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___boxed(lean_object* v_a_4776_, lean_object* v_x_4777_){
_start:
{
uint8_t v_res_4778_; lean_object* v_r_4779_; 
v_res_4778_ = l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(v_a_4776_, v_x_4777_);
lean_dec(v_x_4777_);
lean_dec_ref(v_a_4776_);
v_r_4779_ = lean_box(v_res_4778_);
return v_r_4779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(lean_object* v___x_4780_, lean_object* v_as_4781_, size_t v_sz_4782_, size_t v_i_4783_, lean_object* v_b_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_){
_start:
{
lean_object* v_a_4793_; uint8_t v___x_4797_; 
v___x_4797_ = lean_usize_dec_lt(v_i_4783_, v_sz_4782_);
if (v___x_4797_ == 0)
{
lean_object* v___x_4798_; 
v___x_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4798_, 0, v_b_4784_);
return v___x_4798_;
}
else
{
lean_object* v___x_4799_; lean_object* v_a_4800_; uint8_t v___x_4801_; 
v___x_4799_ = lean_box(0);
v_a_4800_ = lean_array_uget_borrowed(v_as_4781_, v_i_4783_);
v___x_4801_ = l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(v_a_4800_, v___x_4780_);
if (v___x_4801_ == 0)
{
v_a_4793_ = v___x_4799_;
goto v___jp_4792_;
}
else
{
lean_object* v_ref_4802_; lean_object* v_declName_4803_; lean_object* v_fileName_4804_; lean_object* v_fileMap_4805_; lean_object* v_options_4806_; lean_object* v_currRecDepth_4807_; lean_object* v_maxRecDepth_4808_; lean_object* v_ref_4809_; lean_object* v_currNamespace_4810_; lean_object* v_openDecls_4811_; lean_object* v_initHeartbeats_4812_; lean_object* v_maxHeartbeats_4813_; lean_object* v_quotContext_4814_; lean_object* v_currMacroScope_4815_; uint8_t v_diag_4816_; lean_object* v_cancelTk_x3f_4817_; uint8_t v_suppressElabErrors_4818_; lean_object* v_inheritedTraceOptions_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v_ref_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; 
v_ref_4802_ = lean_ctor_get(v_a_4800_, 0);
v_declName_4803_ = lean_ctor_get(v_a_4800_, 3);
v_fileName_4804_ = lean_ctor_get(v___y_4789_, 0);
v_fileMap_4805_ = lean_ctor_get(v___y_4789_, 1);
v_options_4806_ = lean_ctor_get(v___y_4789_, 2);
v_currRecDepth_4807_ = lean_ctor_get(v___y_4789_, 3);
v_maxRecDepth_4808_ = lean_ctor_get(v___y_4789_, 4);
v_ref_4809_ = lean_ctor_get(v___y_4789_, 5);
v_currNamespace_4810_ = lean_ctor_get(v___y_4789_, 6);
v_openDecls_4811_ = lean_ctor_get(v___y_4789_, 7);
v_initHeartbeats_4812_ = lean_ctor_get(v___y_4789_, 8);
v_maxHeartbeats_4813_ = lean_ctor_get(v___y_4789_, 9);
v_quotContext_4814_ = lean_ctor_get(v___y_4789_, 10);
v_currMacroScope_4815_ = lean_ctor_get(v___y_4789_, 11);
v_diag_4816_ = lean_ctor_get_uint8(v___y_4789_, sizeof(void*)*14);
v_cancelTk_x3f_4817_ = lean_ctor_get(v___y_4789_, 12);
v_suppressElabErrors_4818_ = lean_ctor_get_uint8(v___y_4789_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4819_ = lean_ctor_get(v___y_4789_, 13);
v___x_4820_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
lean_inc(v_declName_4803_);
v___x_4821_ = l_Lean_MessageData_ofName(v_declName_4803_);
v___x_4822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4820_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
v___x_4823_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_4824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4822_);
lean_ctor_set(v___x_4824_, 1, v___x_4823_);
v_ref_4825_ = l_Lean_replaceRef(v_ref_4802_, v_ref_4809_);
lean_inc_ref(v_inheritedTraceOptions_4819_);
lean_inc(v_cancelTk_x3f_4817_);
lean_inc(v_currMacroScope_4815_);
lean_inc(v_quotContext_4814_);
lean_inc(v_maxHeartbeats_4813_);
lean_inc(v_initHeartbeats_4812_);
lean_inc(v_openDecls_4811_);
lean_inc(v_currNamespace_4810_);
lean_inc(v_maxRecDepth_4808_);
lean_inc(v_currRecDepth_4807_);
lean_inc_ref(v_options_4806_);
lean_inc_ref(v_fileMap_4805_);
lean_inc_ref(v_fileName_4804_);
v___x_4826_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4826_, 0, v_fileName_4804_);
lean_ctor_set(v___x_4826_, 1, v_fileMap_4805_);
lean_ctor_set(v___x_4826_, 2, v_options_4806_);
lean_ctor_set(v___x_4826_, 3, v_currRecDepth_4807_);
lean_ctor_set(v___x_4826_, 4, v_maxRecDepth_4808_);
lean_ctor_set(v___x_4826_, 5, v_ref_4825_);
lean_ctor_set(v___x_4826_, 6, v_currNamespace_4810_);
lean_ctor_set(v___x_4826_, 7, v_openDecls_4811_);
lean_ctor_set(v___x_4826_, 8, v_initHeartbeats_4812_);
lean_ctor_set(v___x_4826_, 9, v_maxHeartbeats_4813_);
lean_ctor_set(v___x_4826_, 10, v_quotContext_4814_);
lean_ctor_set(v___x_4826_, 11, v_currMacroScope_4815_);
lean_ctor_set(v___x_4826_, 12, v_cancelTk_x3f_4817_);
lean_ctor_set(v___x_4826_, 13, v_inheritedTraceOptions_4819_);
lean_ctor_set_uint8(v___x_4826_, sizeof(void*)*14, v_diag_4816_);
lean_ctor_set_uint8(v___x_4826_, sizeof(void*)*14 + 1, v_suppressElabErrors_4818_);
v___x_4827_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_4824_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___x_4826_, v___y_4790_);
lean_dec_ref(v___x_4826_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_dec_ref(v___x_4827_);
v_a_4793_ = v___x_4799_;
goto v___jp_4792_;
}
else
{
return v___x_4827_;
}
}
}
v___jp_4792_:
{
size_t v___x_4794_; size_t v___x_4795_; 
v___x_4794_ = ((size_t)1ULL);
v___x_4795_ = lean_usize_add(v_i_4783_, v___x_4794_);
v_i_4783_ = v___x_4795_;
v_b_4784_ = v_a_4793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___boxed(lean_object* v___x_4828_, lean_object* v_as_4829_, lean_object* v_sz_4830_, lean_object* v_i_4831_, lean_object* v_b_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
size_t v_sz_boxed_4840_; size_t v_i_boxed_4841_; lean_object* v_res_4842_; 
v_sz_boxed_4840_ = lean_unbox_usize(v_sz_4830_);
lean_dec(v_sz_4830_);
v_i_boxed_4841_ = lean_unbox_usize(v_i_4831_);
lean_dec(v_i_4831_);
v_res_4842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(v___x_4828_, v_as_4829_, v_sz_boxed_4840_, v_i_boxed_4841_, v_b_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
lean_dec_ref(v_as_4829_);
lean_dec(v___x_4828_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(lean_object* v_values_4843_, lean_object* v_fvars_4844_, lean_object* v___x_4845_, lean_object* v___x_4846_, lean_object* v_as_4847_, lean_object* v_i_4848_, lean_object* v_j_4849_, lean_object* v_bs_4850_){
_start:
{
lean_object* v_zero_4852_; uint8_t v_isZero_4853_; 
v_zero_4852_ = lean_unsigned_to_nat(0u);
v_isZero_4853_ = lean_nat_dec_eq(v_i_4848_, v_zero_4852_);
if (v_isZero_4853_ == 1)
{
lean_object* v___x_4854_; 
lean_dec(v_j_4849_);
lean_dec(v_i_4848_);
lean_dec_ref(v___x_4846_);
lean_dec_ref(v___x_4845_);
v___x_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4854_, 0, v_bs_4850_);
return v___x_4854_;
}
else
{
lean_object* v___x_4855_; lean_object* v_ref_4856_; lean_object* v_attrs_4857_; lean_object* v_shortDeclName_4858_; lean_object* v_declName_4859_; lean_object* v_parentName_x3f_4860_; lean_object* v_binderIds_4861_; lean_object* v_binders_4862_; lean_object* v_type_4863_; lean_object* v_mvar_4864_; lean_object* v_termination_4865_; lean_object* v_docString_x3f_4866_; lean_object* v___x_4867_; lean_object* v_one_4868_; lean_object* v_n_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4855_ = lean_array_fget_borrowed(v_as_4847_, v_j_4849_);
v_ref_4856_ = lean_ctor_get(v___x_4855_, 0);
v_attrs_4857_ = lean_ctor_get(v___x_4855_, 1);
v_shortDeclName_4858_ = lean_ctor_get(v___x_4855_, 2);
v_declName_4859_ = lean_ctor_get(v___x_4855_, 3);
v_parentName_x3f_4860_ = lean_ctor_get(v___x_4855_, 4);
v_binderIds_4861_ = lean_ctor_get(v___x_4855_, 5);
v_binders_4862_ = lean_ctor_get(v___x_4855_, 6);
v_type_4863_ = lean_ctor_get(v___x_4855_, 7);
v_mvar_4864_ = lean_ctor_get(v___x_4855_, 8);
v_termination_4865_ = lean_ctor_get(v___x_4855_, 10);
v_docString_x3f_4866_ = lean_ctor_get(v___x_4855_, 11);
v___x_4867_ = l_Lean_instInhabitedExpr;
v_one_4868_ = lean_unsigned_to_nat(1u);
v_n_4869_ = lean_nat_sub(v_i_4848_, v_one_4868_);
lean_dec(v_i_4848_);
v___x_4870_ = lean_array_get_borrowed(v___x_4867_, v_values_4843_, v_j_4849_);
v___x_4871_ = lean_array_get_size(v_binderIds_4861_);
lean_inc_ref(v_termination_4865_);
v___x_4872_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v___x_4871_, v_termination_4865_, v___x_4870_);
v___x_4873_ = lean_array_get_borrowed(v___x_4867_, v_fvars_4844_, v_j_4849_);
v___x_4874_ = l_Lean_Expr_fvarId_x21(v___x_4873_);
v___x_4875_ = l_Lean_Expr_mvarId_x21(v_mvar_4864_);
lean_inc(v_docString_x3f_4866_);
lean_inc(v_binders_4862_);
lean_inc(v___x_4870_);
lean_inc_ref(v_type_4863_);
lean_inc_ref(v___x_4846_);
lean_inc_ref(v___x_4845_);
lean_inc(v_parentName_x3f_4860_);
lean_inc(v_declName_4859_);
lean_inc(v_shortDeclName_4858_);
lean_inc_ref(v_attrs_4857_);
lean_inc(v_ref_4856_);
v___x_4876_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v___x_4876_, 0, v_ref_4856_);
lean_ctor_set(v___x_4876_, 1, v___x_4874_);
lean_ctor_set(v___x_4876_, 2, v_attrs_4857_);
lean_ctor_set(v___x_4876_, 3, v_shortDeclName_4858_);
lean_ctor_set(v___x_4876_, 4, v_declName_4859_);
lean_ctor_set(v___x_4876_, 5, v_parentName_x3f_4860_);
lean_ctor_set(v___x_4876_, 6, v___x_4845_);
lean_ctor_set(v___x_4876_, 7, v___x_4846_);
lean_ctor_set(v___x_4876_, 8, v_type_4863_);
lean_ctor_set(v___x_4876_, 9, v___x_4870_);
lean_ctor_set(v___x_4876_, 10, v___x_4875_);
lean_ctor_set(v___x_4876_, 11, v___x_4872_);
lean_ctor_set(v___x_4876_, 12, v_binders_4862_);
lean_ctor_set(v___x_4876_, 13, v_docString_x3f_4866_);
v___x_4877_ = lean_nat_add(v_j_4849_, v_one_4868_);
lean_dec(v_j_4849_);
v___x_4878_ = lean_array_push(v_bs_4850_, v___x_4876_);
v_i_4848_ = v_n_4869_;
v_j_4849_ = v___x_4877_;
v_bs_4850_ = v___x_4878_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg___boxed(lean_object* v_values_4880_, lean_object* v_fvars_4881_, lean_object* v___x_4882_, lean_object* v___x_4883_, lean_object* v_as_4884_, lean_object* v_i_4885_, lean_object* v_j_4886_, lean_object* v_bs_4887_, lean_object* v___y_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(v_values_4880_, v_fvars_4881_, v___x_4882_, v___x_4883_, v_as_4884_, v_i_4885_, v_j_4886_, v_bs_4887_);
lean_dec_ref(v_as_4884_);
lean_dec_ref(v_fvars_4881_);
lean_dec_ref(v_values_4880_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(lean_object* v_views_4890_, lean_object* v_fvars_4891_, lean_object* v_values_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v___x_4900_; lean_object* v_letRecsToLift_4901_; lean_object* v___x_4902_; size_t v_sz_4903_; size_t v___x_4904_; lean_object* v___x_4905_; 
v___x_4900_ = lean_st_ref_get(v_a_4894_);
v_letRecsToLift_4901_ = lean_ctor_get(v___x_4900_, 6);
lean_inc(v_letRecsToLift_4901_);
lean_dec(v___x_4900_);
v___x_4902_ = lean_box(0);
v_sz_4903_ = lean_array_size(v_views_4890_);
v___x_4904_ = ((size_t)0ULL);
v___x_4905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(v_letRecsToLift_4901_, v_views_4890_, v_sz_4903_, v___x_4904_, v___x_4902_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_, v_a_4898_);
lean_dec(v_letRecsToLift_4901_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v_lctx_4906_; lean_object* v_localInstances_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4937_; 
lean_dec_ref(v___x_4905_);
v_lctx_4906_ = lean_ctor_get(v_a_4895_, 2);
v_localInstances_4907_ = lean_ctor_get(v_a_4895_, 3);
v___x_4908_ = lean_array_get_size(v_views_4890_);
v___x_4909_ = lean_unsigned_to_nat(0u);
v___x_4910_ = lean_mk_empty_array_with_capacity(v___x_4908_);
lean_inc_ref(v_localInstances_4907_);
lean_inc_ref(v_lctx_4906_);
v___x_4911_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(v_values_4892_, v_fvars_4891_, v_lctx_4906_, v_localInstances_4907_, v_views_4890_, v___x_4908_, v___x_4909_, v___x_4910_);
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4914_ = v___x_4911_;
v_isShared_4915_ = v_isSharedCheck_4937_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4937_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4916_; lean_object* v_levelNames_4917_; lean_object* v_syntheticMVars_4918_; lean_object* v_pendingMVars_4919_; lean_object* v_mvarErrorInfos_4920_; lean_object* v_levelMVarErrorInfos_4921_; lean_object* v_mvarArgNames_4922_; lean_object* v_letRecsToLift_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4936_; 
v___x_4916_ = lean_st_ref_take(v_a_4894_);
v_levelNames_4917_ = lean_ctor_get(v___x_4916_, 0);
v_syntheticMVars_4918_ = lean_ctor_get(v___x_4916_, 1);
v_pendingMVars_4919_ = lean_ctor_get(v___x_4916_, 2);
v_mvarErrorInfos_4920_ = lean_ctor_get(v___x_4916_, 3);
v_levelMVarErrorInfos_4921_ = lean_ctor_get(v___x_4916_, 4);
v_mvarArgNames_4922_ = lean_ctor_get(v___x_4916_, 5);
v_letRecsToLift_4923_ = lean_ctor_get(v___x_4916_, 6);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4925_ = v___x_4916_;
v_isShared_4926_ = v_isSharedCheck_4936_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_letRecsToLift_4923_);
lean_inc(v_mvarArgNames_4922_);
lean_inc(v_levelMVarErrorInfos_4921_);
lean_inc(v_mvarErrorInfos_4920_);
lean_inc(v_pendingMVars_4919_);
lean_inc(v_syntheticMVars_4918_);
lean_inc(v_levelNames_4917_);
lean_dec(v___x_4916_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4936_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4930_; 
v___x_4927_ = lean_array_to_list(v_a_4912_);
v___x_4928_ = l_List_appendTR___redArg(v___x_4927_, v_letRecsToLift_4923_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 6, v___x_4928_);
v___x_4930_ = v___x_4925_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_levelNames_4917_);
lean_ctor_set(v_reuseFailAlloc_4935_, 1, v_syntheticMVars_4918_);
lean_ctor_set(v_reuseFailAlloc_4935_, 2, v_pendingMVars_4919_);
lean_ctor_set(v_reuseFailAlloc_4935_, 3, v_mvarErrorInfos_4920_);
lean_ctor_set(v_reuseFailAlloc_4935_, 4, v_levelMVarErrorInfos_4921_);
lean_ctor_set(v_reuseFailAlloc_4935_, 5, v_mvarArgNames_4922_);
lean_ctor_set(v_reuseFailAlloc_4935_, 6, v___x_4928_);
v___x_4930_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
lean_object* v___x_4931_; lean_object* v___x_4933_; 
v___x_4931_ = lean_st_ref_set(v_a_4894_, v___x_4930_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 0, v___x_4902_);
v___x_4933_ = v___x_4914_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4902_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
}
}
else
{
return v___x_4905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___boxed(lean_object* v_views_4938_, lean_object* v_fvars_4939_, lean_object* v_values_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_){
_start:
{
lean_object* v_res_4948_; 
v_res_4948_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(v_views_4938_, v_fvars_4939_, v_values_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_);
lean_dec(v_a_4946_);
lean_dec_ref(v_a_4945_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
lean_dec_ref(v_values_4940_);
lean_dec_ref(v_fvars_4939_);
lean_dec_ref(v_views_4938_);
return v_res_4948_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2(lean_object* v_values_4949_, lean_object* v_fvars_4950_, lean_object* v___x_4951_, lean_object* v___x_4952_, lean_object* v_as_4953_, lean_object* v_i_4954_, lean_object* v_j_4955_, lean_object* v_inv_4956_, lean_object* v_bs_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(v_values_4949_, v_fvars_4950_, v___x_4951_, v___x_4952_, v_as_4953_, v_i_4954_, v_j_4955_, v_bs_4957_);
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___boxed(lean_object* v_values_4966_, lean_object* v_fvars_4967_, lean_object* v___x_4968_, lean_object* v___x_4969_, lean_object* v_as_4970_, lean_object* v_i_4971_, lean_object* v_j_4972_, lean_object* v_inv_4973_, lean_object* v_bs_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2(v_values_4966_, v_fvars_4967_, v___x_4968_, v___x_4969_, v_as_4970_, v_i_4971_, v_j_4972_, v_inv_4973_, v_bs_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
lean_dec(v___y_4978_);
lean_dec_ref(v___y_4977_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec_ref(v_as_4970_);
lean_dec_ref(v_fvars_4967_);
lean_dec_ref(v_values_4966_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(size_t v_sz_4983_, size_t v_i_4984_, lean_object* v_bs_4985_){
_start:
{
uint8_t v___x_4986_; 
v___x_4986_ = lean_usize_dec_lt(v_i_4984_, v_sz_4983_);
if (v___x_4986_ == 0)
{
return v_bs_4985_;
}
else
{
lean_object* v_v_4987_; lean_object* v_mvar_4988_; lean_object* v___x_4989_; lean_object* v_bs_x27_4990_; size_t v___x_4991_; size_t v___x_4992_; lean_object* v___x_4993_; 
v_v_4987_ = lean_array_uget_borrowed(v_bs_4985_, v_i_4984_);
v_mvar_4988_ = lean_ctor_get(v_v_4987_, 8);
lean_inc_ref(v_mvar_4988_);
v___x_4989_ = lean_unsigned_to_nat(0u);
v_bs_x27_4990_ = lean_array_uset(v_bs_4985_, v_i_4984_, v___x_4989_);
v___x_4991_ = ((size_t)1ULL);
v___x_4992_ = lean_usize_add(v_i_4984_, v___x_4991_);
v___x_4993_ = lean_array_uset(v_bs_x27_4990_, v_i_4984_, v_mvar_4988_);
v_i_4984_ = v___x_4992_;
v_bs_4985_ = v___x_4993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1___boxed(lean_object* v_sz_4995_, lean_object* v_i_4996_, lean_object* v_bs_4997_){
_start:
{
size_t v_sz_boxed_4998_; size_t v_i_boxed_4999_; lean_object* v_res_5000_; 
v_sz_boxed_4998_ = lean_unbox_usize(v_sz_4995_);
lean_dec(v_sz_4995_);
v_i_boxed_4999_ = lean_unbox_usize(v_i_4996_);
lean_dec(v_i_4996_);
v_res_5000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(v_sz_boxed_4998_, v_i_boxed_4999_, v_bs_4997_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(lean_object* v_as_5001_, size_t v_sz_5002_, size_t v_i_5003_, lean_object* v_b_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_){
_start:
{
uint8_t v___x_5012_; 
v___x_5012_ = lean_usize_dec_lt(v_i_5003_, v_sz_5002_);
if (v___x_5012_ == 0)
{
lean_object* v___x_5013_; 
v___x_5013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5013_, 0, v_b_5004_);
return v___x_5013_;
}
else
{
lean_object* v_array_5014_; lean_object* v_start_5015_; lean_object* v_stop_5016_; uint8_t v___x_5017_; 
v_array_5014_ = lean_ctor_get(v_b_5004_, 0);
v_start_5015_ = lean_ctor_get(v_b_5004_, 1);
v_stop_5016_ = lean_ctor_get(v_b_5004_, 2);
v___x_5017_ = lean_nat_dec_lt(v_start_5015_, v_stop_5016_);
if (v___x_5017_ == 0)
{
lean_object* v___x_5018_; 
v___x_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5018_, 0, v_b_5004_);
return v___x_5018_;
}
else
{
lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5042_; 
lean_inc(v_stop_5016_);
lean_inc(v_start_5015_);
lean_inc_ref(v_array_5014_);
v_isSharedCheck_5042_ = !lean_is_exclusive(v_b_5004_);
if (v_isSharedCheck_5042_ == 0)
{
lean_object* v_unused_5043_; lean_object* v_unused_5044_; lean_object* v_unused_5045_; 
v_unused_5043_ = lean_ctor_get(v_b_5004_, 2);
lean_dec(v_unused_5043_);
v_unused_5044_ = lean_ctor_get(v_b_5004_, 1);
lean_dec(v_unused_5044_);
v_unused_5045_ = lean_ctor_get(v_b_5004_, 0);
lean_dec(v_unused_5045_);
v___x_5020_ = v_b_5004_;
v_isShared_5021_ = v_isSharedCheck_5042_;
goto v_resetjp_5019_;
}
else
{
lean_dec(v_b_5004_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5042_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v_a_5022_; lean_object* v_ref_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v_a_5022_ = lean_array_uget_borrowed(v_as_5001_, v_i_5003_);
v_ref_5023_ = lean_ctor_get(v_a_5022_, 0);
v___x_5024_ = lean_array_fget_borrowed(v_array_5014_, v_start_5015_);
lean_inc(v___x_5024_);
lean_inc(v_ref_5023_);
v___x_5025_ = l_Lean_Elab_Term_addLocalVarInfo(v_ref_5023_, v___x_5024_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
if (lean_obj_tag(v___x_5025_) == 0)
{
lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5029_; 
lean_dec_ref(v___x_5025_);
v___x_5026_ = lean_unsigned_to_nat(1u);
v___x_5027_ = lean_nat_add(v_start_5015_, v___x_5026_);
lean_dec(v_start_5015_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set(v___x_5020_, 1, v___x_5027_);
v___x_5029_ = v___x_5020_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_array_5014_);
lean_ctor_set(v_reuseFailAlloc_5033_, 1, v___x_5027_);
lean_ctor_set(v_reuseFailAlloc_5033_, 2, v_stop_5016_);
v___x_5029_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
size_t v___x_5030_; size_t v___x_5031_; 
v___x_5030_ = ((size_t)1ULL);
v___x_5031_ = lean_usize_add(v_i_5003_, v___x_5030_);
v_i_5003_ = v___x_5031_;
v_b_5004_ = v___x_5029_;
goto _start;
}
}
else
{
lean_object* v_a_5034_; lean_object* v___x_5036_; uint8_t v_isShared_5037_; uint8_t v_isSharedCheck_5041_; 
lean_del_object(v___x_5020_);
lean_dec(v_stop_5016_);
lean_dec(v_start_5015_);
lean_dec_ref(v_array_5014_);
v_a_5034_ = lean_ctor_get(v___x_5025_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5025_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5036_ = v___x_5025_;
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
else
{
lean_inc(v_a_5034_);
lean_dec(v___x_5025_);
v___x_5036_ = lean_box(0);
v_isShared_5037_ = v_isSharedCheck_5041_;
goto v_resetjp_5035_;
}
v_resetjp_5035_:
{
lean_object* v___x_5039_; 
if (v_isShared_5037_ == 0)
{
v___x_5039_ = v___x_5036_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0___boxed(lean_object* v_as_5046_, lean_object* v_sz_5047_, lean_object* v_i_5048_, lean_object* v_b_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
size_t v_sz_boxed_5057_; size_t v_i_boxed_5058_; lean_object* v_res_5059_; 
v_sz_boxed_5057_ = lean_unbox_usize(v_sz_5047_);
lean_dec(v_sz_5047_);
v_i_boxed_5058_ = lean_unbox_usize(v_i_5048_);
lean_dec(v_i_5048_);
v_res_5059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(v_as_5046_, v_sz_boxed_5057_, v_i_boxed_5058_, v_b_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec_ref(v_as_5046_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0(lean_object* v_decls_5060_, lean_object* v_a_5061_, lean_object* v_body_5062_, lean_object* v_expectedType_x3f_5063_, lean_object* v_fvars_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_){
_start:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; size_t v_sz_5075_; size_t v___x_5076_; lean_object* v___x_5077_; 
v___x_5072_ = lean_unsigned_to_nat(0u);
v___x_5073_ = lean_array_get_size(v_fvars_5064_);
lean_inc_ref(v_fvars_5064_);
v___x_5074_ = l_Array_toSubarray___redArg(v_fvars_5064_, v___x_5072_, v___x_5073_);
v_sz_5075_ = lean_array_size(v_decls_5060_);
v___x_5076_ = ((size_t)0ULL);
v___x_5077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(v_decls_5060_, v_sz_5075_, v___x_5076_, v___x_5074_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_);
if (lean_obj_tag(v___x_5077_) == 0)
{
lean_object* v___x_5078_; 
lean_dec_ref(v___x_5077_);
v___x_5078_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(v_a_5061_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v_a_5079_; uint8_t v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; 
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
lean_inc(v_a_5079_);
lean_dec_ref(v___x_5078_);
v___x_5080_ = 1;
v___x_5081_ = lean_box(0);
v___x_5082_ = l_Lean_Elab_Term_elabTermEnsuringType(v_body_5062_, v_expectedType_x3f_5063_, v___x_5080_, v___x_5080_, v___x_5081_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_);
if (lean_obj_tag(v___x_5082_) == 0)
{
lean_object* v_a_5083_; lean_object* v___x_5084_; 
v_a_5083_ = lean_ctor_get(v___x_5082_, 0);
lean_inc(v_a_5083_);
lean_dec_ref(v___x_5082_);
v___x_5084_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(v_decls_5060_, v_fvars_5064_, v_a_5079_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_);
lean_dec(v_a_5079_);
if (lean_obj_tag(v___x_5084_) == 0)
{
uint8_t v___x_5085_; uint8_t v___x_5086_; lean_object* v___x_5087_; 
lean_dec_ref(v___x_5084_);
v___x_5085_ = 0;
v___x_5086_ = 1;
v___x_5087_ = l_Lean_Meta_mkLambdaFVars(v_fvars_5064_, v_a_5083_, v___x_5085_, v___x_5080_, v___x_5085_, v___x_5080_, v___x_5086_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_);
lean_dec_ref(v_fvars_5064_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5097_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5090_ = v___x_5087_;
v_isShared_5091_ = v_isSharedCheck_5097_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5087_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5097_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5095_; 
v___x_5092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(v_sz_5075_, v___x_5076_, v_decls_5060_);
v___x_5093_ = l_Lean_mkAppN(v_a_5088_, v___x_5092_);
lean_dec_ref(v___x_5092_);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 0, v___x_5093_);
v___x_5095_ = v___x_5090_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v___x_5093_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
else
{
lean_dec_ref(v_decls_5060_);
return v___x_5087_;
}
}
else
{
lean_object* v_a_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5105_; 
lean_dec(v_a_5083_);
lean_dec_ref(v_fvars_5064_);
lean_dec_ref(v_decls_5060_);
v_a_5098_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5100_ = v___x_5084_;
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_a_5098_);
lean_dec(v___x_5084_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5105_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v___x_5103_; 
if (v_isShared_5101_ == 0)
{
v___x_5103_ = v___x_5100_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v_a_5098_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
}
else
{
lean_dec(v_a_5079_);
lean_dec_ref(v_fvars_5064_);
lean_dec_ref(v_decls_5060_);
return v___x_5082_;
}
}
else
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5113_; 
lean_dec_ref(v_fvars_5064_);
lean_dec(v_expectedType_x3f_5063_);
lean_dec(v_body_5062_);
lean_dec_ref(v_decls_5060_);
v_a_5106_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5108_ = v___x_5078_;
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5078_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5111_; 
if (v_isShared_5109_ == 0)
{
v___x_5111_ = v___x_5108_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
v___x_5111_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5110_;
}
v_reusejp_5110_:
{
return v___x_5111_;
}
}
}
}
else
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
lean_dec_ref(v_fvars_5064_);
lean_dec(v_expectedType_x3f_5063_);
lean_dec(v_body_5062_);
lean_dec_ref(v_a_5061_);
lean_dec_ref(v_decls_5060_);
v_a_5114_ = lean_ctor_get(v___x_5077_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5077_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5077_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v___x_5119_; 
if (v_isShared_5117_ == 0)
{
v___x_5119_ = v___x_5116_;
goto v_reusejp_5118_;
}
else
{
lean_object* v_reuseFailAlloc_5120_; 
v_reuseFailAlloc_5120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
v___x_5119_ = v_reuseFailAlloc_5120_;
goto v_reusejp_5118_;
}
v_reusejp_5118_:
{
return v___x_5119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0___boxed(lean_object* v_decls_5122_, lean_object* v_a_5123_, lean_object* v_body_5124_, lean_object* v_expectedType_x3f_5125_, lean_object* v_fvars_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Lean_Elab_Term_elabLetRec___lam__0(v_decls_5122_, v_a_5123_, v_body_5124_, v_expectedType_x3f_5125_, v_fvars_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
return v_res_5134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec(lean_object* v_stx_5135_, lean_object* v_expectedType_x3f_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_){
_start:
{
lean_object* v___x_5144_; 
v___x_5144_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(v_stx_5135_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_);
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; lean_object* v_decls_5146_; lean_object* v_body_5147_; lean_object* v___f_5148_; lean_object* v___x_5149_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref(v___x_5144_);
v_decls_5146_ = lean_ctor_get(v_a_5145_, 0);
lean_inc_ref_n(v_decls_5146_, 2);
v_body_5147_ = lean_ctor_get(v_a_5145_, 1);
lean_inc(v_body_5147_);
v___f_5148_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetRec___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5148_, 0, v_decls_5146_);
lean_closure_set(v___f_5148_, 1, v_a_5145_);
lean_closure_set(v___f_5148_, 2, v_body_5147_);
lean_closure_set(v___f_5148_, 3, v_expectedType_x3f_5136_);
v___x_5149_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_decls_5146_, v___f_5148_, v_a_5137_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_);
return v___x_5149_;
}
else
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
lean_dec(v_expectedType_x3f_5136_);
v_a_5150_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v___x_5144_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v___x_5144_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___boxed(lean_object* v_stx_5158_, lean_object* v_expectedType_x3f_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_Elab_Term_elabLetRec(v_stx_5158_, v_expectedType_x3f_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_);
lean_dec(v_a_5165_);
lean_dec_ref(v_a_5164_);
lean_dec(v_a_5163_);
lean_dec_ref(v_a_5162_);
lean_dec(v_a_5161_);
lean_dec_ref(v_a_5160_);
lean_dec(v_stx_5158_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1(){
_start:
{
lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; 
v___x_5181_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5182_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1));
v___x_5183_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3));
v___x_5184_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetRec___boxed), 9, 0);
v___x_5185_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5181_, v___x_5182_, v___x_5183_, v___x_5184_);
return v___x_5185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___boxed(lean_object* v_a_5186_){
_start:
{
lean_object* v_res_5187_; 
v_res_5187_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1();
return v_res_5187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3(){
_start:
{
lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; 
v___x_5214_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3));
v___x_5215_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6));
v___x_5216_ = l_Lean_addBuiltinDeclarationRanges(v___x_5214_, v___x_5215_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___boxed(lean_object* v_a_5217_){
_start:
{
lean_object* v_res_5218_; 
v_res_5218_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3();
return v_res_5218_;
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
