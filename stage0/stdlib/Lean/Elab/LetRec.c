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
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Unknown attribute `["};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]`"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6_value;
static const lean_string_object l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unknown attribute"};
static const lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8;
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__19;
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
lean_dec_ref(v_a_297_);
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
lean_dec_ref(v_a_303_);
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
lean_object* v___x_457_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v_partialFixpoint_x3f_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v_term_x3f_523_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v_term_x3f_539_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v_term_x3f_555_; lean_object* v___y_560_; lean_object* v_val_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v_terminationBy_x3f_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v_terminationBy_x3f_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; uint8_t v___y_629_; uint8_t v___y_630_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_671_; lean_object* v___y_672_; uint8_t v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; uint8_t v___y_685_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v_s_700_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v_val_735_; lean_object* v___y_736_; lean_object* v_terminationBy_x3f_x3f_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v_d_x3f_826_; lean_object* v_t_x3f_835_; lean_object* v___x_873_; uint8_t v___x_874_; 
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
lean_inc(v___y_464_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_459_);
lean_inc_ref(v___y_461_);
lean_inc(v___y_463_);
lean_inc_ref(v___y_462_);
v___x_469_ = lean_apply_7(v___y_468_, v___y_462_, v___y_463_, v___y_461_, v___y_459_, v___y_466_, v___y_464_, lean_box(0));
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
lean_ctor_set(v___x_475_, 1, v___y_465_);
lean_ctor_set(v___x_475_, 2, v___y_467_);
lean_ctor_set(v___x_475_, 3, v___y_460_);
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
lean_dec(v___y_467_);
lean_dec(v___y_465_);
lean_dec(v___y_460_);
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
lean_ctor_set(v___x_501_, 1, v___y_491_);
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
lean_dec_ref(v___y_490_);
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
v___y_459_ = v___y_497_;
v___y_460_ = v_partialFixpoint_x3f_493_;
v___y_461_ = v___y_496_;
v___y_462_ = v___y_494_;
v___y_463_ = v___y_495_;
v___y_464_ = v___y_499_;
v___y_465_ = v___y_491_;
v___y_466_ = v___y_498_;
v___y_467_ = v___y_492_;
v___y_468_ = v___x_507_;
goto v___jp_458_;
}
else
{
lean_object* v_tactic_508_; lean_object* v___x_509_; lean_object* v___f_510_; 
v_tactic_508_ = l_Lean_Syntax_getArg(v_val_503_, v___y_489_);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v_val_503_);
lean_ctor_set(v___x_509_, 1, v_tactic_508_);
v___f_510_ = lean_alloc_closure((void*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_510_, 0, v___x_509_);
v___y_459_ = v___y_497_;
v___y_460_ = v_partialFixpoint_x3f_493_;
v___y_461_ = v___y_496_;
v___y_462_ = v___y_494_;
v___y_463_ = v___y_495_;
v___y_464_ = v___y_499_;
v___y_465_ = v___y_491_;
v___y_466_ = v___y_498_;
v___y_467_ = v___y_492_;
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
lean_ctor_set(v___x_525_, 0, v___y_520_);
lean_ctor_set(v___x_525_, 1, v_term_x3f_523_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*2, v___x_524_);
v___x_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___y_489_ = v___y_513_;
v___y_490_ = v___y_519_;
v___y_491_ = v___y_521_;
v___y_492_ = v___y_522_;
v_partialFixpoint_x3f_493_ = v___x_526_;
v___y_494_ = v___y_516_;
v___y_495_ = v___y_515_;
v___y_496_ = v___y_518_;
v___y_497_ = v___y_514_;
v___y_498_ = v___y_512_;
v___y_499_ = v___y_517_;
goto v___jp_488_;
}
v___jp_527_:
{
uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = 1;
v___x_541_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_541_, 0, v___y_536_);
lean_ctor_set(v___x_541_, 1, v_term_x3f_539_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*2, v___x_540_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v___y_489_ = v___y_529_;
v___y_490_ = v___y_535_;
v___y_491_ = v___y_537_;
v___y_492_ = v___y_538_;
v_partialFixpoint_x3f_493_ = v___x_542_;
v___y_494_ = v___y_532_;
v___y_495_ = v___y_531_;
v___y_496_ = v___y_534_;
v___y_497_ = v___y_530_;
v___y_498_ = v___y_528_;
v___y_499_ = v___y_533_;
goto v___jp_488_;
}
v___jp_543_:
{
uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = 2;
v___x_557_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_557_, 0, v___y_552_);
lean_ctor_set(v___x_557_, 1, v_term_x3f_555_);
lean_ctor_set_uint8(v___x_557_, sizeof(void*)*2, v___x_556_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___y_489_ = v___y_545_;
v___y_490_ = v___y_551_;
v___y_491_ = v___y_553_;
v___y_492_ = v___y_554_;
v_partialFixpoint_x3f_493_ = v___x_558_;
v___y_494_ = v___y_548_;
v___y_495_ = v___y_547_;
v___y_496_ = v___y_550_;
v___y_497_ = v___y_546_;
v___y_498_ = v___y_544_;
v___y_499_ = v___y_549_;
goto v___jp_488_;
}
v___jp_559_:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__12));
lean_inc(v_val_561_);
v___x_572_ = l_Lean_Syntax_isOfKind(v_val_561_, v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__14));
lean_inc(v_val_561_);
v___x_574_ = l_Lean_Syntax_isOfKind(v_val_561_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__16));
lean_inc(v_val_561_);
v___x_576_ = l_Lean_Syntax_isOfKind(v_val_561_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec(v_val_561_);
v___x_577_ = lean_box(0);
v___y_489_ = v___y_560_;
v___y_490_ = v___y_562_;
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
v___x_578_ = l_Lean_Syntax_getArg(v_val_561_, v___y_560_);
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
lean_dec(v_val_561_);
v___x_582_ = lean_box(0);
v___y_489_ = v___y_560_;
v___y_490_ = v___y_562_;
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
v_term_x3f_583_ = l_Lean_Syntax_getArg(v___x_578_, v___y_560_);
lean_dec(v___x_578_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_term_x3f_583_);
v___y_544_ = v___y_569_;
v___y_545_ = v___y_560_;
v___y_546_ = v___y_568_;
v___y_547_ = v___y_566_;
v___y_548_ = v___y_565_;
v___y_549_ = v___y_570_;
v___y_550_ = v___y_567_;
v___y_551_ = v___y_562_;
v___y_552_ = v_val_561_;
v___y_553_ = v___y_563_;
v___y_554_ = v_terminationBy_x3f_564_;
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
v___y_545_ = v___y_560_;
v___y_546_ = v___y_568_;
v___y_547_ = v___y_566_;
v___y_548_ = v___y_565_;
v___y_549_ = v___y_570_;
v___y_550_ = v___y_567_;
v___y_551_ = v___y_562_;
v___y_552_ = v_val_561_;
v___y_553_ = v___y_563_;
v___y_554_ = v_terminationBy_x3f_564_;
v_term_x3f_555_ = v___x_585_;
goto v___jp_543_;
}
}
}
else
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = l_Lean_Syntax_getArg(v_val_561_, v___y_560_);
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
lean_dec(v_val_561_);
v___x_590_ = lean_box(0);
v___y_489_ = v___y_560_;
v___y_490_ = v___y_562_;
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
v_term_x3f_591_ = l_Lean_Syntax_getArg(v___x_586_, v___y_560_);
lean_dec(v___x_586_);
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_term_x3f_591_);
v___y_528_ = v___y_569_;
v___y_529_ = v___y_560_;
v___y_530_ = v___y_568_;
v___y_531_ = v___y_566_;
v___y_532_ = v___y_565_;
v___y_533_ = v___y_570_;
v___y_534_ = v___y_567_;
v___y_535_ = v___y_562_;
v___y_536_ = v_val_561_;
v___y_537_ = v___y_563_;
v___y_538_ = v_terminationBy_x3f_564_;
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
v___y_529_ = v___y_560_;
v___y_530_ = v___y_568_;
v___y_531_ = v___y_566_;
v___y_532_ = v___y_565_;
v___y_533_ = v___y_570_;
v___y_534_ = v___y_567_;
v___y_535_ = v___y_562_;
v___y_536_ = v_val_561_;
v___y_537_ = v___y_563_;
v___y_538_ = v_terminationBy_x3f_564_;
v_term_x3f_539_ = v___x_593_;
goto v___jp_527_;
}
}
}
else
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = l_Lean_Syntax_getArg(v_val_561_, v___y_560_);
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
lean_dec(v_val_561_);
v___x_598_ = lean_box(0);
v___y_489_ = v___y_560_;
v___y_490_ = v___y_562_;
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
v_term_x3f_599_ = l_Lean_Syntax_getArg(v___x_594_, v___y_560_);
lean_dec(v___x_594_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_term_x3f_599_);
v___y_512_ = v___y_569_;
v___y_513_ = v___y_560_;
v___y_514_ = v___y_568_;
v___y_515_ = v___y_566_;
v___y_516_ = v___y_565_;
v___y_517_ = v___y_570_;
v___y_518_ = v___y_567_;
v___y_519_ = v___y_562_;
v___y_520_ = v_val_561_;
v___y_521_ = v___y_563_;
v___y_522_ = v_terminationBy_x3f_564_;
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
v___y_513_ = v___y_560_;
v___y_514_ = v___y_568_;
v___y_515_ = v___y_566_;
v___y_516_ = v___y_565_;
v___y_517_ = v___y_570_;
v___y_518_ = v___y_567_;
v___y_519_ = v___y_562_;
v___y_520_ = v_val_561_;
v___y_521_ = v___y_563_;
v___y_522_ = v_terminationBy_x3f_564_;
v_term_x3f_523_ = v___x_601_;
goto v___jp_511_;
}
}
}
v___jp_602_:
{
if (lean_obj_tag(v___y_604_) == 1)
{
lean_object* v_val_614_; 
v_val_614_ = lean_ctor_get(v___y_604_, 0);
lean_inc(v_val_614_);
lean_dec_ref(v___y_604_);
v___y_560_ = v___y_603_;
v_val_561_ = v_val_614_;
v___y_562_ = v___y_605_;
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
lean_dec(v___y_604_);
v___x_615_ = lean_box(0);
v___y_489_ = v___y_603_;
v___y_490_ = v___y_605_;
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
lean_ctor_set(v___x_632_, 0, v___y_617_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
lean_ctor_set(v___x_632_, 2, v___y_622_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3, v___y_630_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3 + 1, v___y_629_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___y_603_ = v___y_619_;
v___y_604_ = v___y_621_;
v___y_605_ = v___y_626_;
v___y_606_ = v___y_627_;
v_terminationBy_x3f_607_ = v___x_633_;
v___y_608_ = v___y_623_;
v___y_609_ = v___y_620_;
v___y_610_ = v___y_628_;
v___y_611_ = v___y_618_;
v___y_612_ = v___y_624_;
v___y_613_ = v___y_625_;
goto v___jp_602_;
}
v___jp_634_:
{
lean_object* v___x_645_; 
v___x_645_ = lean_box(0);
v___y_603_ = v___y_636_;
v___y_604_ = v___y_639_;
v___y_605_ = v___y_643_;
v___y_606_ = v___y_644_;
v_terminationBy_x3f_607_ = v___x_645_;
v___y_608_ = v___y_641_;
v___y_609_ = v___y_638_;
v___y_610_ = v___y_637_;
v___y_611_ = v___y_635_;
v___y_612_ = v___y_640_;
v___y_613_ = v___y_642_;
goto v___jp_602_;
}
v___jp_646_:
{
lean_object* v___x_657_; 
v___x_657_ = lean_box(0);
v___y_603_ = v___y_648_;
v___y_604_ = v___y_651_;
v___y_605_ = v___y_655_;
v___y_606_ = v___y_656_;
v_terminationBy_x3f_607_ = v___x_657_;
v___y_608_ = v___y_653_;
v___y_609_ = v___y_650_;
v___y_610_ = v___y_649_;
v___y_611_ = v___y_647_;
v___y_612_ = v___y_652_;
v___y_613_ = v___y_654_;
goto v___jp_602_;
}
v___jp_658_:
{
lean_object* v___x_669_; 
v___x_669_ = lean_box(0);
v___y_603_ = v___y_660_;
v___y_604_ = v___y_663_;
v___y_605_ = v___y_667_;
v___y_606_ = v___y_668_;
v_terminationBy_x3f_607_ = v___x_669_;
v___y_608_ = v___y_665_;
v___y_609_ = v___y_662_;
v___y_610_ = v___y_661_;
v___y_611_ = v___y_659_;
v___y_612_ = v___y_664_;
v___y_613_ = v___y_666_;
goto v___jp_602_;
}
v___jp_670_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_686_, 0, v___y_671_);
lean_ctor_set(v___x_686_, 1, v___y_682_);
lean_ctor_set(v___x_686_, 2, v___y_684_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*3, v___y_685_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*3 + 1, v___y_673_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___y_603_ = v___y_674_;
v___y_604_ = v___y_676_;
v___y_605_ = v___y_680_;
v___y_606_ = v___y_681_;
v_terminationBy_x3f_607_ = v___x_687_;
v___y_608_ = v___y_677_;
v___y_609_ = v___y_675_;
v___y_610_ = v___y_683_;
v___y_611_ = v___y_672_;
v___y_612_ = v___y_678_;
v___y_613_ = v___y_679_;
goto v___jp_602_;
}
v___jp_688_:
{
lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(2u);
v___x_702_ = l_Lean_Syntax_getArg(v___y_690_, v___x_701_);
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
lean_dec(v___y_699_);
lean_dec(v___y_698_);
lean_dec(v___y_694_);
lean_dec(v_stx_423_);
v___x_705_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__19);
v___x_706_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___y_690_, v___x_705_, v___y_696_, v___y_693_, v___y_692_, v___y_689_, v___y_695_, v___y_697_);
lean_dec(v___y_690_);
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
v_body_716_ = l_Lean_Syntax_getArg(v___y_690_, v___x_715_);
if (lean_obj_tag(v_s_700_) == 0)
{
v___y_617_ = v___y_690_;
v___y_618_ = v___y_689_;
v___y_619_ = v___y_691_;
v___y_620_ = v___y_693_;
v___y_621_ = v___y_694_;
v___y_622_ = v_body_716_;
v___y_623_ = v___y_696_;
v___y_624_ = v___y_695_;
v___y_625_ = v___y_697_;
v___y_626_ = v___y_698_;
v___y_627_ = v___y_699_;
v___y_628_ = v___y_692_;
v___y_629_ = v___x_703_;
v___y_630_ = v___x_703_;
goto v___jp_616_;
}
else
{
lean_dec_ref(v_s_700_);
v___y_617_ = v___y_690_;
v___y_618_ = v___y_689_;
v___y_619_ = v___y_691_;
v___y_620_ = v___y_693_;
v___y_621_ = v___y_694_;
v___y_622_ = v_body_716_;
v___y_623_ = v___y_696_;
v___y_624_ = v___y_695_;
v___y_625_ = v___y_697_;
v___y_626_ = v___y_698_;
v___y_627_ = v___y_699_;
v___y_628_ = v___y_692_;
v___y_629_ = v___x_703_;
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
v_body_720_ = l_Lean_Syntax_getArg(v___y_690_, v___x_719_);
v_vars_721_ = l_Lean_Syntax_getArgs(v___x_717_);
lean_dec(v___x_717_);
if (lean_obj_tag(v_s_700_) == 0)
{
v___y_671_ = v___y_690_;
v___y_672_ = v___y_689_;
v___y_673_ = v___x_718_;
v___y_674_ = v___y_691_;
v___y_675_ = v___y_693_;
v___y_676_ = v___y_694_;
v___y_677_ = v___y_696_;
v___y_678_ = v___y_695_;
v___y_679_ = v___y_697_;
v___y_680_ = v___y_698_;
v___y_681_ = v___y_699_;
v___y_682_ = v_vars_721_;
v___y_683_ = v___y_692_;
v___y_684_ = v_body_720_;
v___y_685_ = v___x_718_;
goto v___jp_670_;
}
else
{
lean_dec_ref(v_s_700_);
v___y_671_ = v___y_690_;
v___y_672_ = v___y_689_;
v___y_673_ = v___x_718_;
v___y_674_ = v___y_691_;
v___y_675_ = v___y_693_;
v___y_676_ = v___y_694_;
v___y_677_ = v___y_696_;
v___y_678_ = v___y_695_;
v___y_679_ = v___y_697_;
v___y_680_ = v___y_698_;
v___y_681_ = v___y_699_;
v___y_682_ = v_vars_721_;
v___y_683_ = v___y_692_;
v___y_684_ = v_body_720_;
v___y_685_ = v___x_703_;
goto v___jp_670_;
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v___x_717_);
lean_dec(v_s_700_);
lean_dec(v___y_699_);
lean_dec(v___y_698_);
lean_dec(v___y_694_);
lean_dec(v_stx_423_);
v___x_722_ = lean_obj_once(&l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21, &l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21_once, _init_l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__21);
v___x_723_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___y_690_, v___x_722_, v___y_696_, v___y_693_, v___y_692_, v___y_689_, v___y_695_, v___y_697_);
lean_dec(v___y_690_);
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
lean_dec(v___y_736_);
lean_dec(v___y_734_);
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
v___x_764_ = l_Lean_Syntax_getArg(v_val_735_, v___y_733_);
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
lean_dec(v___y_736_);
lean_dec(v___y_734_);
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
v___y_659_ = v___y_741_;
v___y_660_ = v___y_733_;
v___y_661_ = v___y_740_;
v___y_662_ = v___y_739_;
v___y_663_ = v___y_734_;
v___y_664_ = v___y_742_;
v___y_665_ = v___y_738_;
v___y_666_ = v___y_743_;
v___y_667_ = v___y_736_;
v___y_668_ = v_terminationBy_x3f_x3f_737_;
goto v___jp_658_;
}
}
else
{
lean_dec(v___x_764_);
lean_dec(v_val_735_);
v___y_659_ = v___y_741_;
v___y_660_ = v___y_733_;
v___y_661_ = v___y_740_;
v___y_662_ = v___y_739_;
v___y_663_ = v___y_734_;
v___y_664_ = v___y_742_;
v___y_665_ = v___y_738_;
v___y_666_ = v___y_743_;
v___y_667_ = v___y_736_;
v___y_668_ = v_terminationBy_x3f_x3f_737_;
goto v___jp_658_;
}
}
}
else
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = l_Lean_Syntax_getArg(v_val_735_, v___y_733_);
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
lean_dec(v___y_736_);
lean_dec(v___y_734_);
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
v___y_647_ = v___y_741_;
v___y_648_ = v___y_733_;
v___y_649_ = v___y_740_;
v___y_650_ = v___y_739_;
v___y_651_ = v___y_734_;
v___y_652_ = v___y_742_;
v___y_653_ = v___y_738_;
v___y_654_ = v___y_743_;
v___y_655_ = v___y_736_;
v___y_656_ = v_terminationBy_x3f_x3f_737_;
goto v___jp_646_;
}
}
else
{
lean_dec(v___x_778_);
lean_dec(v_val_735_);
v___y_647_ = v___y_741_;
v___y_648_ = v___y_733_;
v___y_649_ = v___y_740_;
v___y_650_ = v___y_739_;
v___y_651_ = v___y_734_;
v___y_652_ = v___y_742_;
v___y_653_ = v___y_738_;
v___y_654_ = v___y_743_;
v___y_655_ = v___y_736_;
v___y_656_ = v_terminationBy_x3f_x3f_737_;
goto v___jp_646_;
}
}
}
else
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = l_Lean_Syntax_getArg(v_val_735_, v___y_733_);
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
lean_dec(v___y_736_);
lean_dec(v___y_734_);
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
v___y_635_ = v___y_741_;
v___y_636_ = v___y_733_;
v___y_637_ = v___y_740_;
v___y_638_ = v___y_739_;
v___y_639_ = v___y_734_;
v___y_640_ = v___y_742_;
v___y_641_ = v___y_738_;
v___y_642_ = v___y_743_;
v___y_643_ = v___y_736_;
v___y_644_ = v_terminationBy_x3f_x3f_737_;
goto v___jp_634_;
}
}
else
{
lean_dec(v___x_792_);
lean_dec(v_val_735_);
v___y_635_ = v___y_741_;
v___y_636_ = v___y_733_;
v___y_637_ = v___y_740_;
v___y_638_ = v___y_739_;
v___y_639_ = v___y_734_;
v___y_640_ = v___y_742_;
v___y_641_ = v___y_738_;
v___y_642_ = v___y_743_;
v___y_643_ = v___y_736_;
v___y_644_ = v_terminationBy_x3f_x3f_737_;
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
v_val_561_ = v_val_735_;
v___y_562_ = v___y_736_;
v___y_563_ = v_terminationBy_x3f_x3f_737_;
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
v___x_807_ = l_Lean_Syntax_getArg(v_val_735_, v___y_733_);
v___x_808_ = l_Lean_Syntax_isNone(v___x_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; 
lean_inc(v___x_807_);
v___x_809_ = l_Lean_Syntax_matchesNull(v___x_807_, v___y_733_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___x_807_);
lean_dec(v_terminationBy_x3f_x3f_737_);
lean_dec(v___y_736_);
lean_dec(v___y_734_);
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
v___y_689_ = v___y_741_;
v___y_690_ = v_val_735_;
v___y_691_ = v___y_733_;
v___y_692_ = v___y_740_;
v___y_693_ = v___y_739_;
v___y_694_ = v___y_734_;
v___y_695_ = v___y_742_;
v___y_696_ = v___y_738_;
v___y_697_ = v___y_743_;
v___y_698_ = v___y_736_;
v___y_699_ = v_terminationBy_x3f_x3f_737_;
v_s_700_ = v___x_821_;
goto v___jp_688_;
}
}
else
{
lean_object* v___x_822_; 
lean_dec(v___x_807_);
v___x_822_ = lean_box(0);
v___y_689_ = v___y_741_;
v___y_690_ = v_val_735_;
v___y_691_ = v___y_733_;
v___y_692_ = v___y_740_;
v___y_693_ = v___y_739_;
v___y_694_ = v___y_734_;
v___y_695_ = v___y_742_;
v___y_696_ = v___y_738_;
v___y_697_ = v___y_743_;
v___y_698_ = v___y_736_;
v___y_699_ = v_terminationBy_x3f_x3f_737_;
v_s_700_ = v___x_822_;
goto v___jp_688_;
}
}
}
v___jp_823_:
{
if (lean_obj_tag(v___y_825_) == 1)
{
lean_object* v_val_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v_val_827_ = lean_ctor_get(v___y_825_, 0);
lean_inc_n(v_val_827_, 2);
v___x_828_ = ((lean_object*)(l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3___closed__25));
v___x_829_ = l_Lean_Syntax_isOfKind(v_val_827_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
v___x_830_ = lean_box(0);
v___y_733_ = v___y_824_;
v___y_734_ = v___y_825_;
v_val_735_ = v_val_827_;
v___y_736_ = v_d_x3f_826_;
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
v___y_733_ = v___y_824_;
v___y_734_ = v___y_825_;
v_val_735_ = v_val_827_;
v___y_736_ = v_d_x3f_826_;
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
if (lean_obj_tag(v___y_825_) == 1)
{
lean_object* v_val_833_; 
v_val_833_ = lean_ctor_get(v___y_825_, 0);
lean_inc(v_val_833_);
v___y_733_ = v___y_824_;
v___y_734_ = v___y_825_;
v_val_735_ = v_val_833_;
v___y_736_ = v_d_x3f_826_;
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
v___y_603_ = v___y_824_;
v___y_604_ = v___y_825_;
v___y_605_ = v_d_x3f_826_;
v___y_606_ = v___x_832_;
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
v___y_824_ = v___x_836_;
v___y_825_ = v_t_x3f_835_;
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
v___y_824_ = v___x_836_;
v___y_825_ = v_t_x3f_835_;
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
uint8_t v___y_52613__boxed_942_; uint8_t v_suppressElabErrors_boxed_943_; uint8_t v_res_944_; lean_object* v_r_945_; 
v___y_52613__boxed_942_ = lean_unbox(v___y_939_);
v_suppressElabErrors_boxed_943_ = lean_unbox(v_suppressElabErrors_940_);
v_res_944_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___lam__0(v___y_52613__boxed_942_, v_suppressElabErrors_boxed_943_, v_x_941_);
lean_dec(v_x_941_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(lean_object* v_ref_947_, lean_object* v_msgData_948_, uint8_t v_severity_949_, uint8_t v_isSilent_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
uint8_t v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; uint8_t v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_993_; lean_object* v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; uint8_t v___y_997_; uint8_t v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1018_; lean_object* v___y_1019_; uint8_t v___y_1020_; uint8_t v___y_1021_; uint8_t v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1029_; lean_object* v___y_1030_; uint8_t v___y_1031_; uint8_t v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; uint8_t v___y_1035_; uint8_t v___x_1040_; lean_object* v___y_1042_; uint8_t v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; uint8_t v___y_1047_; uint8_t v___y_1048_; uint8_t v___y_1050_; uint8_t v___x_1065_; 
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
lean_ctor_set(v___x_982_, 1, v___y_959_);
lean_inc_ref(v___y_958_);
lean_inc_ref(v___y_963_);
v___x_983_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_983_, 0, v___y_963_);
lean_ctor_set(v___x_983_, 1, v___y_961_);
lean_ctor_set(v___x_983_, 2, v___y_962_);
lean_ctor_set(v___x_983_, 3, v___y_958_);
lean_ctor_set(v___x_983_, 4, v___x_982_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*5, v___y_960_);
lean_ctor_set_uint8(v___x_983_, sizeof(void*)*5 + 1, v___y_957_);
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
lean_inc_ref_n(v___y_994_, 2);
v___x_1007_ = l_Lean_FileMap_toPosition(v___y_994_, v___y_996_);
lean_dec(v___y_996_);
v___x_1008_ = l_Lean_FileMap_toPosition(v___y_994_, v___y_1000_);
lean_dec(v___y_1000_);
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0));
if (v___y_997_ == 0)
{
lean_del_object(v___x_1005_);
lean_dec_ref(v___y_993_);
v___y_957_ = v___y_995_;
v___y_958_ = v___x_1010_;
v___y_959_ = v_a_1003_;
v___y_960_ = v___y_998_;
v___y_961_ = v___x_1007_;
v___y_962_ = v___x_1009_;
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
lean_dec_ref(v___x_1009_);
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
v___y_958_ = v___x_1010_;
v___y_959_ = v_a_1003_;
v___y_960_ = v___y_998_;
v___y_961_ = v___x_1007_;
v___y_962_ = v___x_1009_;
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
v___x_1026_ = l_Lean_Syntax_getTailPos_x3f(v___y_1023_, v___y_1022_);
lean_dec(v___y_1023_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_inc(v___y_1025_);
v___y_993_ = v___y_1018_;
v___y_994_ = v___y_1019_;
v___y_995_ = v___y_1020_;
v___y_996_ = v___y_1025_;
v___y_997_ = v___y_1021_;
v___y_998_ = v___y_1022_;
v___y_999_ = v___y_1024_;
v___y_1000_ = v___y_1025_;
goto v___jp_992_;
}
else
{
lean_object* v_val_1027_; 
v_val_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_val_1027_);
lean_dec_ref(v___x_1026_);
v___y_993_ = v___y_1018_;
v___y_994_ = v___y_1019_;
v___y_995_ = v___y_1020_;
v___y_996_ = v___y_1025_;
v___y_997_ = v___y_1021_;
v___y_998_ = v___y_1022_;
v___y_999_ = v___y_1024_;
v___y_1000_ = v_val_1027_;
goto v___jp_992_;
}
}
v___jp_1028_:
{
lean_object* v_ref_1036_; lean_object* v___x_1037_; 
v_ref_1036_ = l_Lean_replaceRef(v_ref_947_, v___y_1034_);
v___x_1037_ = l_Lean_Syntax_getPos_x3f(v_ref_1036_, v___y_1032_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_unsigned_to_nat(0u);
v___y_1018_ = v___y_1029_;
v___y_1019_ = v___y_1030_;
v___y_1020_ = v___y_1035_;
v___y_1021_ = v___y_1031_;
v___y_1022_ = v___y_1032_;
v___y_1023_ = v_ref_1036_;
v___y_1024_ = v___y_1033_;
v___y_1025_ = v___x_1038_;
goto v___jp_1017_;
}
else
{
lean_object* v_val_1039_; 
v_val_1039_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1039_);
lean_dec_ref(v___x_1037_);
v___y_1018_ = v___y_1029_;
v___y_1019_ = v___y_1030_;
v___y_1020_ = v___y_1035_;
v___y_1021_ = v___y_1031_;
v___y_1022_ = v___y_1032_;
v___y_1023_ = v_ref_1036_;
v___y_1024_ = v___y_1033_;
v___y_1025_ = v_val_1039_;
goto v___jp_1017_;
}
}
v___jp_1041_:
{
if (v___y_1048_ == 0)
{
v___y_1029_ = v___y_1044_;
v___y_1030_ = v___y_1042_;
v___y_1031_ = v___y_1043_;
v___y_1032_ = v___y_1047_;
v___y_1033_ = v___y_1045_;
v___y_1034_ = v___y_1046_;
v___y_1035_ = v_severity_949_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v___y_1044_;
v___y_1030_ = v___y_1042_;
v___y_1031_ = v___y_1043_;
v___y_1032_ = v___y_1047_;
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
v___y_1042_ = v_fileMap_1052_;
v___y_1043_ = v_suppressElabErrors_1055_;
v___y_1044_ = v___f_1058_;
v___y_1045_ = v_fileName_1051_;
v___y_1046_ = v_ref_1054_;
v___y_1047_ = v___y_1050_;
v___y_1048_ = v___x_1060_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1061_ = l_Lean_warningAsError;
v___x_1062_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_options_1053_, v___x_1061_);
v___y_1042_ = v_fileMap_1052_;
v___y_1043_ = v_suppressElabErrors_1055_;
v___y_1044_ = v___f_1058_;
v___y_1045_ = v_fileName_1051_;
v___y_1046_ = v_ref_1054_;
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
lean_dec_ref(v_ex_1149_);
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
lean_dec_ref(v_ex_1149_);
v___y_1162_ = v___x_1185_;
goto v___jp_1161_;
}
else
{
lean_dec_ref(v_ex_1149_);
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
lean_dec_ref(v___x_1163_);
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0(void){
_start:
{
size_t v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; 
v___x_1225_ = ((size_t)5ULL);
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_shift_left(v___x_1226_, v___x_1225_);
return v___x_1227_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1(void){
_start:
{
size_t v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; 
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__0);
v___x_1230_ = lean_usize_sub(v___x_1229_, v___x_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(lean_object* v_x_1231_, size_t v_x_1232_, lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1231_) == 0)
{
lean_object* v_es_1234_; lean_object* v___x_1235_; size_t v___x_1236_; size_t v___x_1237_; size_t v___x_1238_; lean_object* v_j_1239_; lean_object* v___x_1240_; 
v_es_1234_ = lean_ctor_get(v_x_1231_, 0);
v___x_1235_ = lean_box(2);
v___x_1236_ = ((size_t)5ULL);
v___x_1237_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___closed__1);
v___x_1238_ = lean_usize_land(v_x_1232_, v___x_1237_);
v_j_1239_ = lean_usize_to_nat(v___x_1238_);
v___x_1240_ = lean_array_get_borrowed(v___x_1235_, v_es_1234_, v_j_1239_);
lean_dec(v_j_1239_);
switch(lean_obj_tag(v___x_1240_))
{
case 0:
{
lean_object* v_key_1241_; uint8_t v___x_1242_; 
v_key_1241_ = lean_ctor_get(v___x_1240_, 0);
v___x_1242_ = l_Lean_instBEqExtraModUse_beq(v_x_1233_, v_key_1241_);
return v___x_1242_;
}
case 1:
{
lean_object* v_node_1243_; size_t v___x_1244_; 
v_node_1243_ = lean_ctor_get(v___x_1240_, 0);
v___x_1244_ = lean_usize_shift_right(v_x_1232_, v___x_1236_);
v_x_1231_ = v_node_1243_;
v_x_1232_ = v___x_1244_;
goto _start;
}
default: 
{
uint8_t v___x_1246_; 
v___x_1246_ = 0;
return v___x_1246_;
}
}
}
else
{
lean_object* v_ks_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_ks_1247_ = lean_ctor_get(v_x_1231_, 0);
v___x_1248_ = lean_unsigned_to_nat(0u);
v___x_1249_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(v_ks_1247_, v___x_1248_, v_x_1233_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg___boxed(lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
size_t v_x_53112__boxed_1253_; uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_x_53112__boxed_1253_ = lean_unbox_usize(v_x_1251_);
lean_dec(v_x_1251_);
v_res_1254_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(v_x_1250_, v_x_53112__boxed_1253_, v_x_1252_);
lean_dec_ref(v_x_1252_);
lean_dec_ref(v_x_1250_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
uint64_t v___x_1258_; size_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1258_ = l_Lean_instHashableExtraModUse_hash(v_x_1257_);
v___x_1259_ = lean_uint64_to_usize(v___x_1258_);
v___x_1260_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(v_x_1256_, v___x_1259_, v_x_1257_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg___boxed(lean_object* v_x_1261_, lean_object* v_x_1262_){
_start:
{
uint8_t v_res_1263_; lean_object* v_r_1264_; 
v_res_1263_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(v_x_1261_, v_x_1262_);
lean_dec_ref(v_x_1262_);
lean_dec_ref(v_x_1261_);
v_r_1264_ = lean_box(v_res_1263_);
return v_r_1264_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1265_; double v___x_1266_; 
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_float_of_nat(v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(lean_object* v_cls_1269_, lean_object* v_msg_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_ref_1276_; lean_object* v___x_1277_; lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1322_; 
v_ref_1276_ = lean_ctor_get(v___y_1273_, 5);
v___x_1277_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__16(v_msg_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1322_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1322_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v_traceState_1283_; lean_object* v_env_1284_; lean_object* v_nextMacroScope_1285_; lean_object* v_ngen_1286_; lean_object* v_auxDeclNGen_1287_; lean_object* v_cache_1288_; lean_object* v_messages_1289_; lean_object* v_infoState_1290_; lean_object* v_snapshotTasks_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1321_; 
v___x_1282_ = lean_st_ref_take(v___y_1274_);
v_traceState_1283_ = lean_ctor_get(v___x_1282_, 4);
v_env_1284_ = lean_ctor_get(v___x_1282_, 0);
v_nextMacroScope_1285_ = lean_ctor_get(v___x_1282_, 1);
v_ngen_1286_ = lean_ctor_get(v___x_1282_, 2);
v_auxDeclNGen_1287_ = lean_ctor_get(v___x_1282_, 3);
v_cache_1288_ = lean_ctor_get(v___x_1282_, 5);
v_messages_1289_ = lean_ctor_get(v___x_1282_, 6);
v_infoState_1290_ = lean_ctor_get(v___x_1282_, 7);
v_snapshotTasks_1291_ = lean_ctor_get(v___x_1282_, 8);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1293_ = v___x_1282_;
v_isShared_1294_ = v_isSharedCheck_1321_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_snapshotTasks_1291_);
lean_inc(v_infoState_1290_);
lean_inc(v_messages_1289_);
lean_inc(v_cache_1288_);
lean_inc(v_traceState_1283_);
lean_inc(v_auxDeclNGen_1287_);
lean_inc(v_ngen_1286_);
lean_inc(v_nextMacroScope_1285_);
lean_inc(v_env_1284_);
lean_dec(v___x_1282_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1321_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
uint64_t v_tid_1295_; lean_object* v_traces_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1320_; 
v_tid_1295_ = lean_ctor_get_uint64(v_traceState_1283_, sizeof(void*)*1);
v_traces_1296_ = lean_ctor_get(v_traceState_1283_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_traceState_1283_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1298_ = v_traceState_1283_;
v_isShared_1299_ = v_isSharedCheck_1320_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_traces_1296_);
lean_dec(v_traceState_1283_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1320_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; double v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1300_ = lean_box(0);
v___x_1301_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__0);
v___x_1302_ = 0;
v___x_1303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0));
v___x_1304_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1304_, 0, v_cls_1269_);
lean_ctor_set(v___x_1304_, 1, v___x_1300_);
lean_ctor_set(v___x_1304_, 2, v___x_1303_);
lean_ctor_set_float(v___x_1304_, sizeof(void*)*3, v___x_1301_);
lean_ctor_set_float(v___x_1304_, sizeof(void*)*3 + 8, v___x_1301_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*3 + 16, v___x_1302_);
v___x_1305_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___closed__1));
v___x_1306_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v_a_1278_);
lean_ctor_set(v___x_1306_, 2, v___x_1305_);
lean_inc(v_ref_1276_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_ref_1276_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = l_Lean_PersistentArray_push___redArg(v_traces_1296_, v___x_1307_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1308_);
v___x_1310_ = v___x_1298_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1308_);
lean_ctor_set_uint64(v_reuseFailAlloc_1319_, sizeof(void*)*1, v_tid_1295_);
v___x_1310_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v___x_1310_);
v___x_1312_ = v___x_1293_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_env_1284_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_nextMacroScope_1285_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_ngen_1286_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_auxDeclNGen_1287_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1318_, 5, v_cache_1288_);
lean_ctor_set(v_reuseFailAlloc_1318_, 6, v_messages_1289_);
lean_ctor_set(v_reuseFailAlloc_1318_, 7, v_infoState_1290_);
lean_ctor_set(v_reuseFailAlloc_1318_, 8, v_snapshotTasks_1291_);
v___x_1312_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1313_ = lean_st_ref_set(v___y_1274_, v___x_1312_);
v___x_1314_ = lean_box(0);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1314_);
v___x_1316_ = v___x_1280_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg___boxed(lean_object* v_cls_1323_, lean_object* v_msg_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_1323_, v_msg_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1330_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__1));
v___x_1334_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__0));
v___x_1335_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_1334_, v___x_1333_);
return v___x_1335_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__5));
v___x_1341_ = l_Lean_stringToMessageData(v___x_1340_);
return v___x_1341_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__7));
v___x_1344_ = l_Lean_stringToMessageData(v___x_1343_);
return v___x_1344_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg___closed__0));
v___x_1346_ = l_Lean_stringToMessageData(v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11(void){
_start:
{
lean_object* v_cls_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_cls_1349_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__4));
v___x_1350_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__10));
v___x_1351_ = l_Lean_Name_append(v___x_1350_, v_cls_1349_);
return v___x_1351_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__12));
v___x_1354_ = l_Lean_stringToMessageData(v___x_1353_);
return v___x_1354_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__14));
v___x_1357_ = l_Lean_stringToMessageData(v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(lean_object* v_mod_1362_, uint8_t v_isMeta_1363_, lean_object* v_hint_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; lean_object* v_env_1373_; uint8_t v_isExporting_1374_; lean_object* v___x_1375_; lean_object* v_env_1376_; lean_object* v___x_1377_; lean_object* v_entry_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1372_ = lean_st_ref_get(v___y_1370_);
v_env_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc_ref(v_env_1373_);
lean_dec(v___x_1372_);
v_isExporting_1374_ = lean_ctor_get_uint8(v_env_1373_, sizeof(void*)*8);
lean_dec_ref(v_env_1373_);
v___x_1375_ = lean_st_ref_get(v___y_1370_);
v_env_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_ref(v_env_1376_);
lean_dec(v___x_1375_);
v___x_1377_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__2);
lean_inc(v_mod_1362_);
v_entry_1378_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1378_, 0, v_mod_1362_);
lean_ctor_set_uint8(v_entry_1378_, sizeof(void*)*1, v_isExporting_1374_);
lean_ctor_set_uint8(v_entry_1378_, sizeof(void*)*1 + 1, v_isMeta_1363_);
v___x_1379_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1380_ = lean_box(1);
v___x_1381_ = lean_box(0);
v___x_1424_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1377_, v___x_1379_, v_env_1376_, v___x_1380_, v___x_1381_);
v___x_1425_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(v___x_1424_, v_entry_1378_);
lean_dec(v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v_options_1426_; uint8_t v_hasTrace_1427_; 
v_options_1426_ = lean_ctor_get(v___y_1369_, 2);
v_hasTrace_1427_ = lean_ctor_get_uint8(v_options_1426_, sizeof(void*)*1);
if (v_hasTrace_1427_ == 0)
{
lean_dec(v_hint_1364_);
lean_dec(v_mod_1362_);
v___y_1383_ = v___y_1368_;
v___y_1384_ = v___y_1370_;
goto v___jp_1382_;
}
else
{
lean_object* v_inheritedTraceOptions_1428_; lean_object* v_cls_1429_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_inheritedTraceOptions_1428_ = lean_ctor_get(v___y_1369_, 13);
v_cls_1429_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__4));
v___x_1449_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__11);
v___x_1450_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1428_, v_options_1426_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_dec(v_hint_1364_);
lean_dec(v_mod_1362_);
v___y_1383_ = v___y_1368_;
v___y_1384_ = v___y_1370_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1451_; lean_object* v___y_1453_; 
v___x_1451_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__13);
if (v_isExporting_1374_ == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__18));
v___y_1453_ = v___x_1460_;
goto v___jp_1452_;
}
else
{
lean_object* v___x_1461_; 
v___x_1461_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__19));
v___y_1453_ = v___x_1461_;
goto v___jp_1452_;
}
v___jp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_inc_ref(v___y_1453_);
v___x_1454_ = l_Lean_stringToMessageData(v___y_1453_);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1451_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__15);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
if (v_isMeta_1363_ == 0)
{
lean_object* v___x_1458_; 
v___x_1458_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__16));
v___y_1436_ = v___x_1457_;
v___y_1437_ = v___x_1458_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1459_; 
v___x_1459_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__17));
v___y_1436_ = v___x_1457_;
v___y_1437_ = v___x_1459_;
goto v___jp_1435_;
}
}
}
v___jp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1431_);
lean_ctor_set(v___x_1433_, 1, v___y_1432_);
v___x_1434_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_1429_, v___x_1433_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_dec_ref(v___x_1434_);
v___y_1383_ = v___y_1368_;
v___y_1384_ = v___y_1370_;
goto v___jp_1382_;
}
else
{
lean_dec_ref(v_entry_1378_);
return v___x_1434_;
}
}
v___jp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
lean_inc_ref(v___y_1437_);
v___x_1438_ = l_Lean_stringToMessageData(v___y_1437_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___y_1436_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__6);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_MessageData_ofName(v_mod_1362_);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l_Lean_Name_isAnonymous(v_hint_1364_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__8);
v___x_1446_ = l_Lean_MessageData_ofName(v_hint_1364_);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___y_1431_ = v___x_1443_;
v___y_1432_ = v___x_1447_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1448_; 
lean_dec(v_hint_1364_);
v___x_1448_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__9);
v___y_1431_ = v___x_1443_;
v___y_1432_ = v___x_1448_;
goto v___jp_1430_;
}
}
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref(v_entry_1378_);
lean_dec(v_hint_1364_);
lean_dec(v_mod_1362_);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
v___jp_1382_:
{
lean_object* v___x_1385_; lean_object* v_toEnvExtension_1386_; lean_object* v_env_1387_; lean_object* v_nextMacroScope_1388_; lean_object* v_ngen_1389_; lean_object* v_auxDeclNGen_1390_; lean_object* v_traceState_1391_; lean_object* v_messages_1392_; lean_object* v_infoState_1393_; lean_object* v_snapshotTasks_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1422_; 
v___x_1385_ = lean_st_ref_take(v___y_1384_);
v_toEnvExtension_1386_ = lean_ctor_get(v___x_1379_, 0);
v_env_1387_ = lean_ctor_get(v___x_1385_, 0);
v_nextMacroScope_1388_ = lean_ctor_get(v___x_1385_, 1);
v_ngen_1389_ = lean_ctor_get(v___x_1385_, 2);
v_auxDeclNGen_1390_ = lean_ctor_get(v___x_1385_, 3);
v_traceState_1391_ = lean_ctor_get(v___x_1385_, 4);
v_messages_1392_ = lean_ctor_get(v___x_1385_, 6);
v_infoState_1393_ = lean_ctor_get(v___x_1385_, 7);
v_snapshotTasks_1394_ = lean_ctor_get(v___x_1385_, 8);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v___x_1385_, 5);
lean_dec(v_unused_1423_);
v___x_1396_ = v___x_1385_;
v_isShared_1397_ = v_isSharedCheck_1422_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_snapshotTasks_1394_);
lean_inc(v_infoState_1393_);
lean_inc(v_messages_1392_);
lean_inc(v_traceState_1391_);
lean_inc(v_auxDeclNGen_1390_);
lean_inc(v_ngen_1389_);
lean_inc(v_nextMacroScope_1388_);
lean_inc(v_env_1387_);
lean_dec(v___x_1385_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1422_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_asyncMode_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v_asyncMode_1398_ = lean_ctor_get(v_toEnvExtension_1386_, 2);
v___x_1399_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1379_, v_env_1387_, v_entry_1378_, v_asyncMode_1398_, v___x_1381_);
v___x_1400_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 5, v___x_1400_);
lean_ctor_set(v___x_1396_, 0, v___x_1399_);
v___x_1402_ = v___x_1396_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_nextMacroScope_1388_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_ngen_1389_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_auxDeclNGen_1390_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_traceState_1391_);
lean_ctor_set(v_reuseFailAlloc_1421_, 5, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1421_, 6, v_messages_1392_);
lean_ctor_set(v_reuseFailAlloc_1421_, 7, v_infoState_1393_);
lean_ctor_set(v_reuseFailAlloc_1421_, 8, v_snapshotTasks_1394_);
v___x_1402_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v_mctx_1405_; lean_object* v_zetaDeltaFVarIds_1406_; lean_object* v_postponed_1407_; lean_object* v_diag_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1419_; 
v___x_1403_ = lean_st_ref_set(v___y_1384_, v___x_1402_);
v___x_1404_ = lean_st_ref_take(v___y_1383_);
v_mctx_1405_ = lean_ctor_get(v___x_1404_, 0);
v_zetaDeltaFVarIds_1406_ = lean_ctor_get(v___x_1404_, 2);
v_postponed_1407_ = lean_ctor_get(v___x_1404_, 3);
v_diag_1408_ = lean_ctor_get(v___x_1404_, 4);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v___x_1404_, 1);
lean_dec(v_unused_1420_);
v___x_1410_ = v___x_1404_;
v_isShared_1411_ = v_isSharedCheck_1419_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_diag_1408_);
lean_inc(v_postponed_1407_);
lean_inc(v_zetaDeltaFVarIds_1406_);
lean_inc(v_mctx_1405_);
lean_dec(v___x_1404_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1419_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v___x_1412_);
v___x_1414_ = v___x_1410_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_mctx_1405_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_zetaDeltaFVarIds_1406_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_postponed_1407_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_diag_1408_);
v___x_1414_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_st_ref_set(v___y_1383_, v___x_1414_);
v___x_1416_ = lean_box(0);
v___x_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
return v___x_1417_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___boxed(lean_object* v_mod_1464_, lean_object* v_isMeta_1465_, lean_object* v_hint_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v_isMeta_boxed_1474_; lean_object* v_res_1475_; 
v_isMeta_boxed_1474_ = lean_unbox(v_isMeta_1465_);
v_res_1475_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(v_mod_1464_, v_isMeta_boxed_1474_, v_hint_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(lean_object* v___x_1476_, lean_object* v_declName_1477_, lean_object* v_as_1478_, size_t v_sz_1479_, size_t v_i_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v___x_1489_; 
v___x_1489_ = lean_usize_dec_lt(v_i_1480_, v_sz_1479_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec(v_declName_1477_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v_b_1481_);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; lean_object* v_modules_1492_; lean_object* v___x_1493_; lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v_toImport_1496_; lean_object* v_module_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; 
v___x_1491_ = l_Lean_Environment_header(v___x_1476_);
v_modules_1492_ = lean_ctor_get(v___x_1491_, 3);
lean_inc_ref(v_modules_1492_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1494_ = lean_array_uget_borrowed(v_as_1478_, v_i_1480_);
v___x_1495_ = lean_array_get(v___x_1493_, v_modules_1492_, v_a_1494_);
lean_dec_ref(v_modules_1492_);
v_toImport_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc_ref(v_toImport_1496_);
lean_dec(v___x_1495_);
v_module_1497_ = lean_ctor_get(v_toImport_1496_, 0);
lean_inc(v_module_1497_);
lean_dec_ref(v_toImport_1496_);
v___x_1498_ = 0;
lean_inc(v_declName_1477_);
v___x_1499_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(v_module_1497_, v___x_1498_, v_declName_1477_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1500_; size_t v___x_1501_; size_t v___x_1502_; 
lean_dec_ref(v___x_1499_);
v___x_1500_ = lean_box(0);
v___x_1501_ = ((size_t)1ULL);
v___x_1502_ = lean_usize_add(v_i_1480_, v___x_1501_);
v_i_1480_ = v___x_1502_;
v_b_1481_ = v___x_1500_;
goto _start;
}
else
{
lean_dec(v_declName_1477_);
return v___x_1499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18___boxed(lean_object* v___x_1504_, lean_object* v_declName_1505_, lean_object* v_as_1506_, lean_object* v_sz_1507_, lean_object* v_i_1508_, lean_object* v_b_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
size_t v_sz_boxed_1517_; size_t v_i_boxed_1518_; lean_object* v_res_1519_; 
v_sz_boxed_1517_ = lean_unbox_usize(v_sz_1507_);
lean_dec(v_sz_1507_);
v_i_boxed_1518_ = lean_unbox_usize(v_i_1508_);
lean_dec(v_i_1508_);
v_res_1519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(v___x_1504_, v_declName_1505_, v_as_1506_, v_sz_boxed_1517_, v_i_boxed_1518_, v_b_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec_ref(v_as_1506_);
lean_dec_ref(v___x_1504_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(lean_object* v_a_1520_, lean_object* v_x_1521_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_box(0);
return v___x_1522_;
}
else
{
lean_object* v_key_1523_; lean_object* v_value_1524_; lean_object* v_tail_1525_; uint8_t v___x_1526_; 
v_key_1523_ = lean_ctor_get(v_x_1521_, 0);
v_value_1524_ = lean_ctor_get(v_x_1521_, 1);
v_tail_1525_ = lean_ctor_get(v_x_1521_, 2);
v___x_1526_ = lean_name_eq(v_key_1523_, v_a_1520_);
if (v___x_1526_ == 0)
{
v_x_1521_ = v_tail_1525_;
goto _start;
}
else
{
lean_object* v___x_1528_; 
lean_inc(v_value_1524_);
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_value_1524_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg___boxed(lean_object* v_a_1529_, lean_object* v_x_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(v_a_1529_, v_x_1530_);
lean_dec(v_x_1530_);
lean_dec(v_a_1529_);
return v_res_1531_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_1532_; uint64_t v___x_1533_; 
v___x_1532_ = lean_unsigned_to_nat(1723u);
v___x_1533_ = lean_uint64_of_nat(v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(lean_object* v_m_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v_buckets_1536_; lean_object* v___x_1537_; uint64_t v___y_1539_; 
v_buckets_1536_ = lean_ctor_get(v_m_1534_, 1);
v___x_1537_ = lean_array_get_size(v_buckets_1536_);
if (lean_obj_tag(v_a_1535_) == 0)
{
uint64_t v___x_1553_; 
v___x_1553_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___closed__0);
v___y_1539_ = v___x_1553_;
goto v___jp_1538_;
}
else
{
uint64_t v_hash_1554_; 
v_hash_1554_ = lean_ctor_get_uint64(v_a_1535_, sizeof(void*)*2);
v___y_1539_ = v_hash_1554_;
goto v___jp_1538_;
}
v___jp_1538_:
{
uint64_t v___x_1540_; uint64_t v___x_1541_; uint64_t v_fold_1542_; uint64_t v___x_1543_; uint64_t v___x_1544_; uint64_t v___x_1545_; size_t v___x_1546_; size_t v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1540_ = 32ULL;
v___x_1541_ = lean_uint64_shift_right(v___y_1539_, v___x_1540_);
v_fold_1542_ = lean_uint64_xor(v___y_1539_, v___x_1541_);
v___x_1543_ = 16ULL;
v___x_1544_ = lean_uint64_shift_right(v_fold_1542_, v___x_1543_);
v___x_1545_ = lean_uint64_xor(v_fold_1542_, v___x_1544_);
v___x_1546_ = lean_uint64_to_usize(v___x_1545_);
v___x_1547_ = lean_usize_of_nat(v___x_1537_);
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = lean_usize_sub(v___x_1547_, v___x_1548_);
v___x_1550_ = lean_usize_land(v___x_1546_, v___x_1549_);
v___x_1551_ = lean_array_uget_borrowed(v_buckets_1536_, v___x_1550_);
v___x_1552_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(v_a_1535_, v___x_1551_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg___boxed(lean_object* v_m_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(v_m_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_m_1555_);
return v_res_1557_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__1));
v___x_1561_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__0));
v___x_1562_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_1561_, v___x_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(lean_object* v_declName_1565_, uint8_t v_isMeta_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; lean_object* v_env_1578_; lean_object* v___y_1580_; lean_object* v___x_1593_; 
v___x_1574_ = lean_st_ref_get(v___y_1572_);
v_env_1578_ = lean_ctor_get(v___x_1574_, 0);
lean_inc_ref(v_env_1578_);
lean_dec(v___x_1574_);
v___x_1593_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1578_, v_declName_1565_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_dec_ref(v_env_1578_);
lean_dec(v_declName_1565_);
goto v___jp_1575_;
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1595_; lean_object* v_modules_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v_val_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_val_1594_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = l_Lean_Environment_header(v_env_1578_);
v_modules_1596_ = lean_ctor_get(v___x_1595_, 3);
lean_inc_ref(v_modules_1596_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = lean_array_get_size(v_modules_1596_);
v___x_1598_ = lean_nat_dec_lt(v_val_1594_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_dec_ref(v_modules_1596_);
lean_dec(v_val_1594_);
lean_dec_ref(v_env_1578_);
lean_dec(v_declName_1565_);
goto v___jp_1575_;
}
else
{
lean_object* v___x_1599_; lean_object* v_env_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___y_1604_; 
v___x_1599_ = lean_st_ref_get(v___y_1572_);
v_env_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc_ref(v_env_1600_);
lean_dec(v___x_1599_);
v___x_1601_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__2);
v___x_1602_ = lean_array_fget(v_modules_1596_, v_val_1594_);
lean_dec(v_val_1594_);
lean_dec_ref(v_modules_1596_);
if (v_isMeta_1566_ == 0)
{
lean_dec_ref(v_env_1600_);
v___y_1604_ = v_isMeta_1566_;
goto v___jp_1603_;
}
else
{
uint8_t v___x_1615_; 
lean_inc(v_declName_1565_);
v___x_1615_ = l_Lean_isMarkedMeta(v_env_1600_, v_declName_1565_);
if (v___x_1615_ == 0)
{
v___y_1604_ = v_isMeta_1566_;
goto v___jp_1603_;
}
else
{
uint8_t v___x_1616_; 
v___x_1616_ = 0;
v___y_1604_ = v___x_1616_;
goto v___jp_1603_;
}
}
v___jp_1603_:
{
lean_object* v_toImport_1605_; lean_object* v_module_1606_; lean_object* v___x_1607_; 
v_toImport_1605_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_ref(v_toImport_1605_);
lean_dec(v___x_1602_);
v_module_1606_ = lean_ctor_get(v_toImport_1605_, 0);
lean_inc(v_module_1606_);
lean_dec_ref(v_toImport_1605_);
lean_inc(v_declName_1565_);
v___x_1607_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17(v_module_1606_, v___y_1604_, v_declName_1565_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec_ref(v___x_1607_);
v___x_1608_ = l_Lean_indirectModUseExt;
v___x_1609_ = lean_box(1);
v___x_1610_ = lean_box(0);
lean_inc_ref(v_env_1578_);
v___x_1611_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1601_, v___x_1608_, v_env_1578_, v___x_1609_, v___x_1610_);
v___x_1612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(v___x_1611_, v_declName_1565_);
lean_dec(v___x_1611_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___closed__3));
v___y_1580_ = v___x_1613_;
goto v___jp_1579_;
}
else
{
lean_object* v_val_1614_; 
v_val_1614_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_val_1614_);
lean_dec_ref(v___x_1612_);
v___y_1580_ = v_val_1614_;
goto v___jp_1579_;
}
}
else
{
lean_dec_ref(v_env_1578_);
lean_dec(v_declName_1565_);
return v___x_1607_;
}
}
}
}
v___jp_1575_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1576_);
return v___x_1577_;
}
v___jp_1579_:
{
lean_object* v___x_1581_; size_t v_sz_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1581_ = lean_box(0);
v_sz_1582_ = lean_array_size(v___y_1580_);
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__18(v_env_1578_, v_declName_1565_, v___y_1580_, v_sz_1582_, v___x_1583_, v___x_1581_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v_env_1578_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v___x_1584_, 0);
lean_dec(v_unused_1592_);
v___x_1586_ = v___x_1584_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v___x_1584_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1581_);
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1581_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
else
{
return v___x_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11___boxed(lean_object* v_declName_1617_, lean_object* v_isMeta_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
uint8_t v_isMeta_boxed_1626_; lean_object* v_res_1627_; 
v_isMeta_boxed_1626_ = lean_unbox(v_isMeta_1618_);
v_res_1627_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v_declName_1617_, v_isMeta_boxed_1626_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(lean_object* v_as_x27_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
if (lean_obj_tag(v_as_x27_1628_) == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_b_1629_);
return v___x_1637_;
}
else
{
lean_object* v_head_1638_; lean_object* v_tail_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; 
v_head_1638_ = lean_ctor_get(v_as_x27_1628_, 0);
v_tail_1639_ = lean_ctor_get(v_as_x27_1628_, 1);
v___x_1640_ = 1;
lean_inc(v_head_1638_);
v___x_1641_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v_head_1638_, v___x_1640_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v___x_1642_; 
lean_dec_ref(v___x_1641_);
v___x_1642_ = lean_box(0);
v_as_x27_1628_ = v_tail_1639_;
v_b_1629_ = v___x_1642_;
goto _start;
}
else
{
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg___boxed(lean_object* v_as_x27_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(v_as_x27_1644_, v_b_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v_as_x27_1644_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(lean_object* v_x_1654_, lean_object* v___y_1655_){
_start:
{
if (lean_obj_tag(v_x_1654_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; 
v_a_1656_ = lean_ctor_get(v_x_1654_, 0);
lean_inc(v_a_1656_);
v___x_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1657_, 0, v_a_1656_);
lean_ctor_set(v___x_1657_, 1, v___y_1655_);
return v___x_1657_;
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1659_; 
v_a_1658_ = lean_ctor_get(v_x_1654_, 0);
lean_inc(v_a_1658_);
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v_a_1658_);
lean_ctor_set(v___x_1659_, 1, v___y_1655_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg___boxed(lean_object* v_x_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_x_1660_, v___y_1661_);
lean_dec_ref(v_x_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(lean_object* v_env_1663_, lean_object* v_stx_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1663_, v_stx_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
if (lean_obj_tag(v_a_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1677_; 
v_a_1669_ = lean_ctor_get(v___x_1667_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v___x_1667_, 0);
lean_dec(v_unused_1678_);
v___x_1671_ = v___x_1667_;
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_box(0);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1673_);
v___x_1675_ = v___x_1671_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_a_1669_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_object* v_val_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1707_; 
v_val_1679_ = lean_ctor_get(v_a_1668_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_a_1668_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1681_ = v_a_1668_;
v_isShared_1682_ = v_isSharedCheck_1707_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_val_1679_);
lean_dec(v_a_1668_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1707_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_snd_1683_; 
v_snd_1683_ = lean_ctor_get(v_val_1679_, 1);
lean_inc(v_snd_1683_);
lean_dec(v_val_1679_);
if (lean_obj_tag(v_snd_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1693_; 
lean_del_object(v___x_1681_);
v_a_1684_ = lean_ctor_get(v___x_1667_, 1);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1667_);
v_a_1685_ = lean_ctor_get(v_snd_1683_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_snd_1683_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1687_ = v_snd_1683_;
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v_snd_1683_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1693_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v___x_1690_, v_a_1684_);
lean_dec_ref(v___x_1690_);
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1706_; 
v_a_1694_ = lean_ctor_get(v___x_1667_, 1);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1667_);
v_a_1695_ = lean_ctor_get(v_snd_1683_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_snd_1683_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1697_ = v_snd_1683_;
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v_snd_1683_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v_a_1695_);
v___x_1700_ = v___x_1681_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1700_);
v___x_1702_ = v___x_1697_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v___x_1702_, v_a_1694_);
lean_dec_ref(v___x_1702_);
return v___x_1703_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
v_a_1708_ = lean_ctor_get(v___x_1667_, 0);
v_a_1709_ = lean_ctor_get(v___x_1667_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1667_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_inc(v_a_1708_);
lean_dec(v___x_1667_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1708_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed(lean_object* v_env_1717_, lean_object* v_stx_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0(v_env_1717_, v_stx_1718_, v___y_1719_, v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(lean_object* v_env_1722_, lean_object* v_options_1723_, lean_object* v_currNamespace_1724_, lean_object* v_openDecls_1725_, lean_object* v_n_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = l_Lean_ResolveName_resolveGlobalName(v_env_1722_, v_options_1723_, v_currNamespace_1724_, v_openDecls_1725_, v_n_1726_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed(lean_object* v_env_1731_, lean_object* v_options_1732_, lean_object* v_currNamespace_1733_, lean_object* v_openDecls_1734_, lean_object* v_n_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4(v_env_1731_, v_options_1732_, v_currNamespace_1733_, v_openDecls_1734_, v_n_1735_, v___y_1736_, v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec_ref(v_options_1732_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(lean_object* v_currNamespace_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v_currNamespace_1739_);
lean_ctor_set(v___x_1742_, 1, v___y_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed(lean_object* v_currNamespace_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3(v_currNamespace_1743_, v___y_1744_, v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(lean_object* v_env_1747_, lean_object* v_declName_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_1751_; lean_object* v_env_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; 
v___x_1751_ = 0;
v_env_1752_ = l_Lean_Environment_setExporting(v_env_1747_, v___x_1751_);
lean_inc(v_declName_1748_);
v___x_1753_ = l_Lean_mkPrivateName(v_env_1752_, v_declName_1748_);
v___x_1754_ = 1;
lean_inc_ref(v_env_1752_);
v___x_1755_ = l_Lean_Environment_contains(v_env_1752_, v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1756_ = l_Lean_privateToUserName(v_declName_1748_);
v___x_1757_ = l_Lean_Environment_contains(v_env_1752_, v___x_1756_, v___x_1754_);
v___x_1758_ = lean_box(v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___y_1750_);
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec_ref(v_env_1752_);
lean_dec(v_declName_1748_);
v___x_1760_ = lean_box(v___x_1755_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v___y_1750_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed(lean_object* v_env_1762_, lean_object* v_declName_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1(v_env_1762_, v_declName_1763_, v___y_1764_, v___y_1765_);
lean_dec_ref(v___y_1764_);
return v_res_1766_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = l_Lean_maxRecDepthErrorMessage;
v___x_1773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__3);
v___x_1775_ = l_Lean_MessageData_ofFormat(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__4);
v___x_1777_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__2));
v___x_1778_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
lean_ctor_set(v___x_1778_, 1, v___x_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(lean_object* v_ref_1779_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___closed__5);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v_ref_1779_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg___boxed(lean_object* v_ref_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(v_ref_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(lean_object* v_env_1787_, lean_object* v_currNamespace_1788_, lean_object* v_openDecls_1789_, lean_object* v_n_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = l_Lean_ResolveName_resolveNamespace(v_env_1787_, v_currNamespace_1788_, v_openDecls_1789_, v_n_1790_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
lean_ctor_set(v___x_1794_, 1, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed(lean_object* v_env_1795_, lean_object* v_currNamespace_1796_, lean_object* v_openDecls_1797_, lean_object* v_n_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2(v_env_1795_, v_currNamespace_1796_, v_openDecls_1797_, v_n_1798_, v___y_1799_, v___y_1800_);
lean_dec_ref(v___y_1799_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(lean_object* v_as_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
if (lean_obj_tag(v_as_1802_) == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
else
{
lean_object* v_options_1812_; uint8_t v_hasTrace_1813_; 
v_options_1812_ = lean_ctor_get(v___y_1807_, 2);
v_hasTrace_1813_ = lean_ctor_get_uint8(v_options_1812_, sizeof(void*)*1);
if (v_hasTrace_1813_ == 0)
{
lean_object* v_tail_1814_; 
v_tail_1814_ = lean_ctor_get(v_as_1802_, 1);
lean_inc(v_tail_1814_);
lean_dec_ref(v_as_1802_);
v_as_1802_ = v_tail_1814_;
goto _start;
}
else
{
lean_object* v_head_1816_; lean_object* v_tail_1817_; lean_object* v_fst_1818_; lean_object* v_snd_1819_; lean_object* v_inheritedTraceOptions_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_head_1816_ = lean_ctor_get(v_as_1802_, 0);
lean_inc(v_head_1816_);
v_tail_1817_ = lean_ctor_get(v_as_1802_, 1);
lean_inc(v_tail_1817_);
lean_dec_ref(v_as_1802_);
v_fst_1818_ = lean_ctor_get(v_head_1816_, 0);
lean_inc_n(v_fst_1818_, 2);
v_snd_1819_ = lean_ctor_get(v_head_1816_, 1);
lean_inc(v_snd_1819_);
lean_dec(v_head_1816_);
v_inheritedTraceOptions_1820_ = lean_ctor_get(v___y_1807_, 13);
v___x_1821_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17___closed__10));
v___x_1822_ = l_Lean_Name_append(v___x_1821_, v_fst_1818_);
v___x_1823_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1820_, v_options_1812_, v___x_1822_);
lean_dec(v___x_1822_);
if (v___x_1823_ == 0)
{
lean_dec(v_snd_1819_);
lean_dec(v_fst_1818_);
v_as_1802_ = v_tail_1817_;
goto _start;
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_snd_1819_);
v___x_1826_ = l_Lean_MessageData_ofFormat(v___x_1825_);
v___x_1827_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_fst_1818_, v___x_1826_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_dec_ref(v___x_1827_);
v_as_1802_ = v_tail_1817_;
goto _start;
}
else
{
lean_dec(v_tail_1817_);
return v___x_1827_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13___boxed(lean_object* v_as_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(v_as_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(lean_object* v_x_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___x_1847_; lean_object* v_env_1848_; lean_object* v_options_1849_; lean_object* v_currRecDepth_1850_; lean_object* v_maxRecDepth_1851_; lean_object* v_ref_1852_; lean_object* v_currNamespace_1853_; lean_object* v_openDecls_1854_; lean_object* v_quotContext_1855_; lean_object* v_currMacroScope_1856_; lean_object* v___x_1857_; lean_object* v_nextMacroScope_1858_; lean_object* v___f_1859_; lean_object* v___f_1860_; lean_object* v___f_1861_; lean_object* v___f_1862_; lean_object* v___f_1863_; lean_object* v_methods_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1847_ = lean_st_ref_get(v___y_1845_);
v_env_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc_ref_n(v_env_1848_, 4);
lean_dec(v___x_1847_);
v_options_1849_ = lean_ctor_get(v___y_1844_, 2);
v_currRecDepth_1850_ = lean_ctor_get(v___y_1844_, 3);
v_maxRecDepth_1851_ = lean_ctor_get(v___y_1844_, 4);
v_ref_1852_ = lean_ctor_get(v___y_1844_, 5);
v_currNamespace_1853_ = lean_ctor_get(v___y_1844_, 6);
v_openDecls_1854_ = lean_ctor_get(v___y_1844_, 7);
v_quotContext_1855_ = lean_ctor_get(v___y_1844_, 10);
v_currMacroScope_1856_ = lean_ctor_get(v___y_1844_, 11);
v___x_1857_ = lean_st_ref_get(v___y_1845_);
v_nextMacroScope_1858_ = lean_ctor_get(v___x_1857_, 1);
lean_inc(v_nextMacroScope_1858_);
lean_dec(v___x_1857_);
v___f_1859_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1859_, 0, v_env_1848_);
v___f_1860_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1860_, 0, v_env_1848_);
lean_inc_n(v_openDecls_1854_, 2);
lean_inc_n(v_currNamespace_1853_, 3);
v___f_1861_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1861_, 0, v_env_1848_);
lean_closure_set(v___f_1861_, 1, v_currNamespace_1853_);
lean_closure_set(v___f_1861_, 2, v_openDecls_1854_);
v___f_1862_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1862_, 0, v_currNamespace_1853_);
lean_inc_ref(v_options_1849_);
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1863_, 0, v_env_1848_);
lean_closure_set(v___f_1863_, 1, v_options_1849_);
lean_closure_set(v___f_1863_, 2, v_currNamespace_1853_);
lean_closure_set(v___f_1863_, 3, v_openDecls_1854_);
v_methods_1864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1864_, 0, v___f_1859_);
lean_ctor_set(v_methods_1864_, 1, v___f_1862_);
lean_ctor_set(v_methods_1864_, 2, v___f_1860_);
lean_ctor_set(v_methods_1864_, 3, v___f_1861_);
lean_ctor_set(v_methods_1864_, 4, v___f_1863_);
lean_inc(v_ref_1852_);
lean_inc(v_maxRecDepth_1851_);
lean_inc(v_currRecDepth_1850_);
lean_inc(v_currMacroScope_1856_);
lean_inc(v_quotContext_1855_);
v___x_1865_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1865_, 0, v_methods_1864_);
lean_ctor_set(v___x_1865_, 1, v_quotContext_1855_);
lean_ctor_set(v___x_1865_, 2, v_currMacroScope_1856_);
lean_ctor_set(v___x_1865_, 3, v_currRecDepth_1850_);
lean_ctor_set(v___x_1865_, 4, v_maxRecDepth_1851_);
lean_ctor_set(v___x_1865_, 5, v_ref_1852_);
v___x_1866_ = lean_box(0);
v___x_1867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1867_, 0, v_nextMacroScope_1858_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
lean_ctor_set(v___x_1867_, 2, v___x_1866_);
v___x_1868_ = lean_apply_2(v_x_1839_, v___x_1865_, v___x_1867_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v_a_1870_; lean_object* v_macroScope_1871_; lean_object* v_traceMsgs_1872_; lean_object* v_expandedMacroDecls_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 1);
lean_inc(v_a_1869_);
v_a_1870_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1870_);
lean_dec_ref(v___x_1868_);
v_macroScope_1871_ = lean_ctor_get(v_a_1869_, 0);
lean_inc(v_macroScope_1871_);
v_traceMsgs_1872_ = lean_ctor_get(v_a_1869_, 1);
lean_inc(v_traceMsgs_1872_);
v_expandedMacroDecls_1873_ = lean_ctor_get(v_a_1869_, 2);
lean_inc(v_expandedMacroDecls_1873_);
lean_dec(v_a_1869_);
v___x_1874_ = lean_box(0);
v___x_1875_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(v_expandedMacroDecls_1873_, v___x_1874_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v_expandedMacroDecls_1873_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; lean_object* v_env_1877_; lean_object* v_ngen_1878_; lean_object* v_auxDeclNGen_1879_; lean_object* v_traceState_1880_; lean_object* v_cache_1881_; lean_object* v_messages_1882_; lean_object* v_infoState_1883_; lean_object* v_snapshotTasks_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref(v___x_1875_);
v___x_1876_ = lean_st_ref_take(v___y_1845_);
v_env_1877_ = lean_ctor_get(v___x_1876_, 0);
v_ngen_1878_ = lean_ctor_get(v___x_1876_, 2);
v_auxDeclNGen_1879_ = lean_ctor_get(v___x_1876_, 3);
v_traceState_1880_ = lean_ctor_get(v___x_1876_, 4);
v_cache_1881_ = lean_ctor_get(v___x_1876_, 5);
v_messages_1882_ = lean_ctor_get(v___x_1876_, 6);
v_infoState_1883_ = lean_ctor_get(v___x_1876_, 7);
v_snapshotTasks_1884_ = lean_ctor_get(v___x_1876_, 8);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; 
v_unused_1911_ = lean_ctor_get(v___x_1876_, 1);
lean_dec(v_unused_1911_);
v___x_1886_ = v___x_1876_;
v_isShared_1887_ = v_isSharedCheck_1910_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_snapshotTasks_1884_);
lean_inc(v_infoState_1883_);
lean_inc(v_messages_1882_);
lean_inc(v_cache_1881_);
lean_inc(v_traceState_1880_);
lean_inc(v_auxDeclNGen_1879_);
lean_inc(v_ngen_1878_);
lean_inc(v_env_1877_);
lean_dec(v___x_1876_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1910_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 1, v_macroScope_1871_);
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_env_1877_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_macroScope_1871_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v_ngen_1878_);
lean_ctor_set(v_reuseFailAlloc_1909_, 3, v_auxDeclNGen_1879_);
lean_ctor_set(v_reuseFailAlloc_1909_, 4, v_traceState_1880_);
lean_ctor_set(v_reuseFailAlloc_1909_, 5, v_cache_1881_);
lean_ctor_set(v_reuseFailAlloc_1909_, 6, v_messages_1882_);
lean_ctor_set(v_reuseFailAlloc_1909_, 7, v_infoState_1883_);
lean_ctor_set(v_reuseFailAlloc_1909_, 8, v_snapshotTasks_1884_);
v___x_1889_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_st_ref_set(v___y_1845_, v___x_1889_);
v___x_1891_ = l_List_reverse___redArg(v_traceMsgs_1872_);
v___x_1892_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__13(v___x_1891_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v___x_1892_, 0);
lean_dec(v_unused_1900_);
v___x_1894_ = v___x_1892_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_dec(v___x_1892_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v_a_1870_);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1870_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_a_1870_);
v_a_1901_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1892_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1892_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_traceMsgs_1872_);
lean_dec(v_macroScope_1871_);
lean_dec(v_a_1870_);
v_a_1912_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1875_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1875_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; 
v_a_1920_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1920_);
lean_dec_ref(v___x_1868_);
if (lean_obj_tag(v_a_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_a_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_a_1921_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_a_1921_);
v_a_1922_ = lean_ctor_get(v_a_1920_, 1);
lean_inc_ref(v_a_1922_);
lean_dec_ref(v_a_1920_);
v___x_1923_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___closed__0));
v___x_1924_ = lean_string_dec_eq(v_a_1922_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_a_1922_);
v___x_1926_ = l_Lean_MessageData_ofFormat(v___x_1925_);
v___x_1927_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_a_1921_, v___x_1926_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v_a_1921_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; 
lean_dec_ref(v_a_1922_);
v___x_1928_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(v_a_1921_);
return v___x_1928_;
}
}
else
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
return v___x_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg___boxed(lean_object* v_x_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v_x_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v_res_1938_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__0));
v___x_1941_ = l_Lean_stringToMessageData(v___x_1940_);
return v___x_1941_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__2));
v___x_1944_ = l_Lean_stringToMessageData(v___x_1943_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__7));
v___x_1954_ = l_Lean_stringToMessageData(v___x_1953_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1(lean_object* v___x_1955_, lean_object* v_attrInstance_1956_, lean_object* v___f_1957_, lean_object* v___x_1958_, lean_object* v___x_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_1955_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; lean_object* v_attr_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
v___x_1969_ = lean_unsigned_to_nat(1u);
v_attr_1970_ = l_Lean_Syntax_getArg(v_attrInstance_1956_, v___x_1969_);
v___x_1971_ = lean_alloc_closure((void*)(l_Lean_expandMacros), 4, 2);
lean_closure_set(v___x_1971_, 0, v_attr_1970_);
lean_closure_set(v___x_1971_, 1, v___f_1957_);
v___x_1972_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_1971_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2040_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_2040_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2040_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___y_1978_; lean_object* v_attrName_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
lean_inc(v_a_1973_);
v___x_2021_ = l_Lean_Syntax_getKind(v_a_1973_);
v___x_2022_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__6));
v___x_2023_ = lean_name_eq(v___x_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
if (lean_obj_tag(v___x_2021_) == 1)
{
lean_object* v_str_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v_str_2024_ = lean_ctor_get(v___x_2021_, 1);
lean_inc_ref(v_str_2024_);
lean_dec_ref(v___x_2021_);
v___x_2025_ = lean_box(0);
v___x_2026_ = l_Lean_Name_str___override(v___x_2025_, v_str_2024_);
v_attrName_1985_ = v___x_2026_;
v___y_1986_ = v___y_1960_;
v___y_1987_ = v___y_1961_;
v___y_1988_ = v___y_1962_;
v___y_1989_ = v___y_1963_;
v___y_1990_ = v___y_1964_;
v___y_1991_ = v___y_1965_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v___x_2021_);
lean_del_object(v___x_1975_);
lean_dec(v_a_1968_);
lean_dec(v___x_1958_);
v___x_2027_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__8);
v___x_2028_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_a_1973_, v___x_2027_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v_a_1973_);
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v___x_2021_);
v___x_2037_ = l_Lean_Syntax_getArg(v_a_1973_, v___x_1959_);
v___x_2038_ = l_Lean_Syntax_getId(v___x_2037_);
lean_dec(v___x_2037_);
v___x_2039_ = lean_erase_macro_scopes(v___x_2038_);
v_attrName_1985_ = v___x_2039_;
v___y_1986_ = v___y_1960_;
v___y_1987_ = v___y_1961_;
v___y_1988_ = v___y_1962_;
v___y_1989_ = v___y_1963_;
v___y_1990_ = v___y_1964_;
v___y_1991_ = v___y_1965_;
goto v___jp_1984_;
}
v___jp_1977_:
{
lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1982_; 
v___x_1979_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1979_, 0, v___y_1978_);
lean_ctor_set(v___x_1979_, 1, v_a_1973_);
v___x_1980_ = lean_unbox(v_a_1968_);
lean_dec(v_a_1968_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*2, v___x_1980_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1979_);
v___x_1982_ = v___x_1975_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1979_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
v___jp_1984_:
{
lean_object* v___x_1992_; lean_object* v_env_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_st_ref_get(v___y_1991_);
v_env_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc_ref(v_env_1993_);
lean_dec(v___x_1992_);
lean_inc(v_attrName_1985_);
v___x_1994_ = l_Lean_getAttributeImpl(v_env_1993_, v_attrName_1985_);
if (lean_obj_tag(v___x_1994_) == 1)
{
lean_object* v___x_1995_; lean_object* v_env_1996_; lean_object* v___x_1997_; 
lean_dec_ref(v___x_1994_);
v___x_1995_ = lean_st_ref_get(v___y_1991_);
v_env_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc_ref(v_env_1996_);
lean_dec(v___x_1995_);
lean_inc(v_attrName_1985_);
v___x_1997_ = l_Lean_getAttributeImpl(v_env_1996_, v_attrName_1985_);
if (lean_obj_tag(v___x_1997_) == 1)
{
lean_object* v_a_1998_; lean_object* v___x_1999_; lean_object* v_toAttributeImplCore_2000_; lean_object* v_env_2001_; lean_object* v_ref_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1997_);
v___x_1999_ = lean_st_ref_get(v___y_1991_);
v_toAttributeImplCore_2000_ = lean_ctor_get(v_a_1998_, 0);
lean_inc_ref(v_toAttributeImplCore_2000_);
lean_dec(v_a_1998_);
v_env_2001_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_ref(v_env_2001_);
lean_dec(v___x_1999_);
v_ref_2002_ = lean_ctor_get(v_toAttributeImplCore_2000_, 0);
lean_inc_n(v_ref_2002_, 2);
lean_dec_ref(v_toAttributeImplCore_2000_);
v___x_2003_ = l_Lean_regularInitAttr;
v___x_2004_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_1958_, v___x_2003_, v_env_2001_, v_ref_2002_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_dec(v_ref_2002_);
v___y_1978_ = v_attrName_1985_;
goto v___jp_1977_;
}
else
{
uint8_t v___x_2005_; lean_object* v___x_2006_; 
lean_dec_ref(v___x_2004_);
v___x_2005_ = 1;
v___x_2006_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11(v_ref_2002_, v___x_2005_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_dec_ref(v___x_2006_);
v___y_1978_ = v_attrName_1985_;
goto v___jp_1977_;
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_attrName_1985_);
lean_del_object(v___x_1975_);
lean_dec(v_a_1973_);
lean_dec(v_a_1968_);
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1997_);
lean_dec(v___x_1958_);
v___y_1978_ = v_attrName_1985_;
goto v___jp_1977_;
}
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec_ref(v___x_1994_);
lean_del_object(v___x_1975_);
lean_dec(v_a_1973_);
lean_dec(v_a_1968_);
lean_dec(v___x_1958_);
v___x_2015_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__1);
v___x_2016_ = l_Lean_MessageData_ofName(v_attrName_1985_);
v___x_2017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = lean_obj_once(&l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3, &l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3_once, _init_l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___closed__3);
v___x_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2019_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
return v___x_2020_;
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_a_1968_);
lean_dec(v___x_1958_);
v_a_2041_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_1972_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_1972_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v___x_1958_);
lean_dec_ref(v___f_1957_);
v_a_2049_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_1967_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_1967_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___boxed(lean_object* v___x_2057_, lean_object* v_attrInstance_2058_, lean_object* v___f_2059_, lean_object* v___x_2060_, lean_object* v___x_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1(v___x_2057_, v_attrInstance_2058_, v___f_2059_, v___x_2060_, v___x_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___x_2061_);
lean_dec(v_attrInstance_2058_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(lean_object* v___y_2070_, uint8_t v_isExporting_2071_, lean_object* v___x_2072_, lean_object* v___y_2073_, lean_object* v___x_2074_, lean_object* v_a_x3f_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v_env_2078_; lean_object* v_nextMacroScope_2079_; lean_object* v_ngen_2080_; lean_object* v_auxDeclNGen_2081_; lean_object* v_traceState_2082_; lean_object* v_messages_2083_; lean_object* v_infoState_2084_; lean_object* v_snapshotTasks_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2110_; 
v___x_2077_ = lean_st_ref_take(v___y_2070_);
v_env_2078_ = lean_ctor_get(v___x_2077_, 0);
v_nextMacroScope_2079_ = lean_ctor_get(v___x_2077_, 1);
v_ngen_2080_ = lean_ctor_get(v___x_2077_, 2);
v_auxDeclNGen_2081_ = lean_ctor_get(v___x_2077_, 3);
v_traceState_2082_ = lean_ctor_get(v___x_2077_, 4);
v_messages_2083_ = lean_ctor_get(v___x_2077_, 6);
v_infoState_2084_ = lean_ctor_get(v___x_2077_, 7);
v_snapshotTasks_2085_ = lean_ctor_get(v___x_2077_, 8);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v___x_2077_, 5);
lean_dec(v_unused_2111_);
v___x_2087_ = v___x_2077_;
v_isShared_2088_ = v_isSharedCheck_2110_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_snapshotTasks_2085_);
lean_inc(v_infoState_2084_);
lean_inc(v_messages_2083_);
lean_inc(v_traceState_2082_);
lean_inc(v_auxDeclNGen_2081_);
lean_inc(v_ngen_2080_);
lean_inc(v_nextMacroScope_2079_);
lean_inc(v_env_2078_);
lean_dec(v___x_2077_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2110_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = l_Lean_Environment_setExporting(v_env_2078_, v_isExporting_2071_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 5, v___x_2072_);
lean_ctor_set(v___x_2087_, 0, v___x_2089_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_nextMacroScope_2079_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_ngen_2080_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_auxDeclNGen_2081_);
lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_traceState_2082_);
lean_ctor_set(v_reuseFailAlloc_2109_, 5, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2109_, 6, v_messages_2083_);
lean_ctor_set(v_reuseFailAlloc_2109_, 7, v_infoState_2084_);
lean_ctor_set(v_reuseFailAlloc_2109_, 8, v_snapshotTasks_2085_);
v___x_2091_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v_mctx_2094_; lean_object* v_zetaDeltaFVarIds_2095_; lean_object* v_postponed_2096_; lean_object* v_diag_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2107_; 
v___x_2092_ = lean_st_ref_set(v___y_2070_, v___x_2091_);
v___x_2093_ = lean_st_ref_take(v___y_2073_);
v_mctx_2094_ = lean_ctor_get(v___x_2093_, 0);
v_zetaDeltaFVarIds_2095_ = lean_ctor_get(v___x_2093_, 2);
v_postponed_2096_ = lean_ctor_get(v___x_2093_, 3);
v_diag_2097_ = lean_ctor_get(v___x_2093_, 4);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v___x_2093_, 1);
lean_dec(v_unused_2108_);
v___x_2099_ = v___x_2093_;
v_isShared_2100_ = v_isSharedCheck_2107_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_diag_2097_);
lean_inc(v_postponed_2096_);
lean_inc(v_zetaDeltaFVarIds_2095_);
lean_inc(v_mctx_2094_);
lean_dec(v___x_2093_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2107_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___x_2074_);
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_mctx_2094_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_zetaDeltaFVarIds_2095_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_postponed_2096_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v_diag_2097_);
v___x_2102_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_st_ref_set(v___y_2073_, v___x_2102_);
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0___boxed(lean_object* v___y_2112_, lean_object* v_isExporting_2113_, lean_object* v___x_2114_, lean_object* v___y_2115_, lean_object* v___x_2116_, lean_object* v_a_x3f_2117_, lean_object* v___y_2118_){
_start:
{
uint8_t v_isExporting_boxed_2119_; lean_object* v_res_2120_; 
v_isExporting_boxed_2119_ = lean_unbox(v_isExporting_2113_);
v_res_2120_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(v___y_2112_, v_isExporting_boxed_2119_, v___x_2114_, v___y_2115_, v___x_2116_, v_a_x3f_2117_);
lean_dec(v_a_x3f_2117_);
lean_dec(v___y_2115_);
lean_dec(v___y_2112_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(lean_object* v_x_2121_, uint8_t v_isExporting_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v_env_2131_; uint8_t v_isExporting_2132_; lean_object* v___x_2133_; lean_object* v_env_2134_; lean_object* v_nextMacroScope_2135_; lean_object* v_ngen_2136_; lean_object* v_auxDeclNGen_2137_; lean_object* v_traceState_2138_; lean_object* v_messages_2139_; lean_object* v_infoState_2140_; lean_object* v_snapshotTasks_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2195_; 
v___x_2130_ = lean_st_ref_get(v___y_2128_);
v_env_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc_ref(v_env_2131_);
lean_dec(v___x_2130_);
v_isExporting_2132_ = lean_ctor_get_uint8(v_env_2131_, sizeof(void*)*8);
lean_dec_ref(v_env_2131_);
v___x_2133_ = lean_st_ref_take(v___y_2128_);
v_env_2134_ = lean_ctor_get(v___x_2133_, 0);
v_nextMacroScope_2135_ = lean_ctor_get(v___x_2133_, 1);
v_ngen_2136_ = lean_ctor_get(v___x_2133_, 2);
v_auxDeclNGen_2137_ = lean_ctor_get(v___x_2133_, 3);
v_traceState_2138_ = lean_ctor_get(v___x_2133_, 4);
v_messages_2139_ = lean_ctor_get(v___x_2133_, 6);
v_infoState_2140_ = lean_ctor_get(v___x_2133_, 7);
v_snapshotTasks_2141_ = lean_ctor_get(v___x_2133_, 8);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2195_ == 0)
{
lean_object* v_unused_2196_; 
v_unused_2196_ = lean_ctor_get(v___x_2133_, 5);
lean_dec(v_unused_2196_);
v___x_2143_ = v___x_2133_;
v_isShared_2144_ = v_isSharedCheck_2195_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_snapshotTasks_2141_);
lean_inc(v_infoState_2140_);
lean_inc(v_messages_2139_);
lean_inc(v_traceState_2138_);
lean_inc(v_auxDeclNGen_2137_);
lean_inc(v_ngen_2136_);
lean_inc(v_nextMacroScope_2135_);
lean_inc(v_env_2134_);
lean_dec(v___x_2133_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2195_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2145_ = l_Lean_Environment_setExporting(v_env_2134_, v_isExporting_2122_);
v___x_2146_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 5, v___x_2146_);
lean_ctor_set(v___x_2143_, 0, v___x_2145_);
v___x_2148_ = v___x_2143_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2194_, 1, v_nextMacroScope_2135_);
lean_ctor_set(v_reuseFailAlloc_2194_, 2, v_ngen_2136_);
lean_ctor_set(v_reuseFailAlloc_2194_, 3, v_auxDeclNGen_2137_);
lean_ctor_set(v_reuseFailAlloc_2194_, 4, v_traceState_2138_);
lean_ctor_set(v_reuseFailAlloc_2194_, 5, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2194_, 6, v_messages_2139_);
lean_ctor_set(v_reuseFailAlloc_2194_, 7, v_infoState_2140_);
lean_ctor_set(v_reuseFailAlloc_2194_, 8, v_snapshotTasks_2141_);
v___x_2148_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_mctx_2151_; lean_object* v_zetaDeltaFVarIds_2152_; lean_object* v_postponed_2153_; lean_object* v_diag_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2192_; 
v___x_2149_ = lean_st_ref_set(v___y_2128_, v___x_2148_);
v___x_2150_ = lean_st_ref_take(v___y_2126_);
v_mctx_2151_ = lean_ctor_get(v___x_2150_, 0);
v_zetaDeltaFVarIds_2152_ = lean_ctor_get(v___x_2150_, 2);
v_postponed_2153_ = lean_ctor_get(v___x_2150_, 3);
v_diag_2154_ = lean_ctor_get(v___x_2150_, 4);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; 
v_unused_2193_ = lean_ctor_get(v___x_2150_, 1);
lean_dec(v_unused_2193_);
v___x_2156_ = v___x_2150_;
v_isShared_2157_ = v_isSharedCheck_2192_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_diag_2154_);
lean_inc(v_postponed_2153_);
lean_inc(v_zetaDeltaFVarIds_2152_);
lean_inc(v_mctx_2151_);
lean_dec(v___x_2150_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2192_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v___x_2158_);
v___x_2160_ = v___x_2156_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_mctx_2151_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_zetaDeltaFVarIds_2152_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_postponed_2153_);
lean_ctor_set(v_reuseFailAlloc_2191_, 4, v_diag_2154_);
v___x_2160_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v_r_2162_; 
v___x_2161_ = lean_st_ref_set(v___y_2126_, v___x_2160_);
lean_inc(v___y_2128_);
lean_inc_ref(v___y_2127_);
lean_inc(v___y_2126_);
lean_inc_ref(v___y_2125_);
lean_inc(v___y_2124_);
lean_inc_ref(v___y_2123_);
v_r_2162_ = lean_apply_7(v_x_2121_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, lean_box(0));
if (lean_obj_tag(v_r_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2179_; 
v_a_2163_ = lean_ctor_get(v_r_2162_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_r_2162_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2165_ = v_r_2162_;
v_isShared_2166_ = v_isSharedCheck_2179_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v_r_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2179_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
lean_inc(v_a_2163_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set_tag(v___x_2165_, 1);
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v___x_2169_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(v___y_2128_, v_isExporting_2132_, v___x_2146_, v___y_2126_, v___x_2158_, v___x_2168_);
lean_dec_ref(v___x_2168_);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2176_ == 0)
{
lean_object* v_unused_2177_; 
v_unused_2177_ = lean_ctor_get(v___x_2169_, 0);
lean_dec(v_unused_2177_);
v___x_2171_ = v___x_2169_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_dec(v___x_2169_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v_a_2163_);
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2163_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
v_a_2180_ = lean_ctor_get(v_r_2162_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v_r_2162_);
v___x_2181_ = lean_box(0);
v___x_2182_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___lam__0(v___y_2128_, v_isExporting_2132_, v___x_2146_, v___y_2126_, v___x_2158_, v___x_2181_);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; 
v_unused_2190_ = lean_ctor_get(v___x_2182_, 0);
lean_dec(v_unused_2190_);
v___x_2184_ = v___x_2182_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_dec(v___x_2182_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set_tag(v___x_2184_, 1);
lean_ctor_set(v___x_2184_, 0, v_a_2180_);
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2180_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg___boxed(lean_object* v_x_2197_, lean_object* v_isExporting_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v_isExporting_boxed_2206_; lean_object* v_res_2207_; 
v_isExporting_boxed_2206_ = lean_unbox(v_isExporting_2198_);
v_res_2207_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(v_x_2197_, v_isExporting_boxed_2206_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(lean_object* v_x_2208_, uint8_t v_when_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
if (v_when_2209_ == 0)
{
lean_object* v___x_2217_; 
lean_inc(v___y_2215_);
lean_inc_ref(v___y_2214_);
lean_inc(v___y_2213_);
lean_inc_ref(v___y_2212_);
lean_inc(v___y_2211_);
lean_inc_ref(v___y_2210_);
v___x_2217_ = lean_apply_7(v_x_2208_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, lean_box(0));
return v___x_2217_;
}
else
{
uint8_t v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = 0;
v___x_2219_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(v_x_2208_, v___x_2218_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg___boxed(lean_object* v_x_2220_, lean_object* v_when_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
uint8_t v_when_boxed_2229_; lean_object* v_res_2230_; 
v_when_boxed_2229_ = lean_unbox(v_when_2221_);
v_res_2230_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(v_x_2220_, v_when_boxed_2229_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(lean_object* v_attrInstance_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___f_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; 
v___f_2240_ = ((lean_object*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___closed__0));
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_unsigned_to_nat(0u);
v___x_2243_ = l_Lean_Syntax_getArg(v_attrInstance_2232_, v___x_2242_);
v___x_2244_ = lean_alloc_closure((void*)(l_Lean_Elab_toAttributeKind___boxed), 3, 1);
lean_closure_set(v___x_2244_, 0, v___x_2243_);
v___f_2245_ = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___lam__1___boxed), 12, 5);
lean_closure_set(v___f_2245_, 0, v___x_2244_);
lean_closure_set(v___f_2245_, 1, v_attrInstance_2232_);
lean_closure_set(v___f_2245_, 2, v___f_2240_);
lean_closure_set(v___f_2245_, 3, v___x_2241_);
lean_closure_set(v___f_2245_, 4, v___x_2242_);
v___x_2246_ = 1;
v___x_2247_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(v___f_2245_, v___x_2246_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31___boxed(lean_object* v_attrInstance_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(v_attrInstance_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(lean_object* v_as_2257_, size_t v_sz_2258_, size_t v_i_2259_, lean_object* v_b_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_snd_2269_; uint8_t v___x_2273_; 
v___x_2273_ = lean_usize_dec_lt(v_i_2259_, v_sz_2258_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_b_2260_);
return v___x_2274_;
}
else
{
lean_object* v_fileName_2275_; lean_object* v_fileMap_2276_; lean_object* v_options_2277_; lean_object* v_currRecDepth_2278_; lean_object* v_maxRecDepth_2279_; lean_object* v_ref_2280_; lean_object* v_currNamespace_2281_; lean_object* v_openDecls_2282_; lean_object* v_initHeartbeats_2283_; lean_object* v_maxHeartbeats_2284_; lean_object* v_quotContext_2285_; lean_object* v_currMacroScope_2286_; uint8_t v_diag_2287_; lean_object* v_cancelTk_x3f_2288_; uint8_t v_suppressElabErrors_2289_; lean_object* v_inheritedTraceOptions_2290_; lean_object* v_a_2291_; lean_object* v_ref_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v_fileName_2275_ = lean_ctor_get(v___y_2265_, 0);
v_fileMap_2276_ = lean_ctor_get(v___y_2265_, 1);
v_options_2277_ = lean_ctor_get(v___y_2265_, 2);
v_currRecDepth_2278_ = lean_ctor_get(v___y_2265_, 3);
v_maxRecDepth_2279_ = lean_ctor_get(v___y_2265_, 4);
v_ref_2280_ = lean_ctor_get(v___y_2265_, 5);
v_currNamespace_2281_ = lean_ctor_get(v___y_2265_, 6);
v_openDecls_2282_ = lean_ctor_get(v___y_2265_, 7);
v_initHeartbeats_2283_ = lean_ctor_get(v___y_2265_, 8);
v_maxHeartbeats_2284_ = lean_ctor_get(v___y_2265_, 9);
v_quotContext_2285_ = lean_ctor_get(v___y_2265_, 10);
v_currMacroScope_2286_ = lean_ctor_get(v___y_2265_, 11);
v_diag_2287_ = lean_ctor_get_uint8(v___y_2265_, sizeof(void*)*14);
v_cancelTk_x3f_2288_ = lean_ctor_get(v___y_2265_, 12);
v_suppressElabErrors_2289_ = lean_ctor_get_uint8(v___y_2265_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2290_ = lean_ctor_get(v___y_2265_, 13);
v_a_2291_ = lean_array_uget_borrowed(v_as_2257_, v_i_2259_);
v_ref_2292_ = l_Lean_replaceRef(v_a_2291_, v_ref_2280_);
lean_inc_ref(v_inheritedTraceOptions_2290_);
lean_inc(v_cancelTk_x3f_2288_);
lean_inc(v_currMacroScope_2286_);
lean_inc(v_quotContext_2285_);
lean_inc(v_maxHeartbeats_2284_);
lean_inc(v_initHeartbeats_2283_);
lean_inc(v_openDecls_2282_);
lean_inc(v_currNamespace_2281_);
lean_inc(v_maxRecDepth_2279_);
lean_inc(v_currRecDepth_2278_);
lean_inc_ref(v_options_2277_);
lean_inc_ref(v_fileMap_2276_);
lean_inc_ref(v_fileName_2275_);
v___x_2293_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2293_, 0, v_fileName_2275_);
lean_ctor_set(v___x_2293_, 1, v_fileMap_2276_);
lean_ctor_set(v___x_2293_, 2, v_options_2277_);
lean_ctor_set(v___x_2293_, 3, v_currRecDepth_2278_);
lean_ctor_set(v___x_2293_, 4, v_maxRecDepth_2279_);
lean_ctor_set(v___x_2293_, 5, v_ref_2292_);
lean_ctor_set(v___x_2293_, 6, v_currNamespace_2281_);
lean_ctor_set(v___x_2293_, 7, v_openDecls_2282_);
lean_ctor_set(v___x_2293_, 8, v_initHeartbeats_2283_);
lean_ctor_set(v___x_2293_, 9, v_maxHeartbeats_2284_);
lean_ctor_set(v___x_2293_, 10, v_quotContext_2285_);
lean_ctor_set(v___x_2293_, 11, v_currMacroScope_2286_);
lean_ctor_set(v___x_2293_, 12, v_cancelTk_x3f_2288_);
lean_ctor_set(v___x_2293_, 13, v_inheritedTraceOptions_2290_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*14, v_diag_2287_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*14 + 1, v_suppressElabErrors_2289_);
lean_inc(v_a_2291_);
v___x_2294_ = l_Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31(v_a_2291_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___x_2293_, v___y_2266_);
lean_dec_ref(v___x_2293_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2294_);
v___x_2296_ = lean_array_push(v_b_2260_, v_a_2295_);
v_snd_2269_ = v___x_2296_;
goto v___jp_2268_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2317_; 
v_a_2297_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2299_ = v___x_2294_;
v_isShared_2300_ = v_isSharedCheck_2317_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2294_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2317_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
uint8_t v___y_2302_; uint8_t v___x_2315_; 
v___x_2315_ = l_Lean_Exception_isInterrupt(v_a_2297_);
if (v___x_2315_ == 0)
{
uint8_t v___x_2316_; 
lean_inc(v_a_2297_);
v___x_2316_ = l_Lean_Exception_isRuntime(v_a_2297_);
v___y_2302_ = v___x_2316_;
goto v___jp_2301_;
}
else
{
v___y_2302_ = v___x_2315_;
goto v___jp_2301_;
}
v___jp_2301_:
{
if (v___y_2302_ == 0)
{
lean_object* v___x_2303_; 
lean_del_object(v___x_2299_);
v___x_2303_ = l_Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32(v_a_2297_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_dec_ref(v___x_2303_);
v_snd_2269_ = v_b_2260_;
goto v___jp_2268_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v_b_2260_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_object* v___x_2313_; 
lean_dec_ref(v_b_2260_);
if (v_isShared_2300_ == 0)
{
v___x_2313_ = v___x_2299_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2297_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
v___jp_2268_:
{
size_t v___x_2270_; size_t v___x_2271_; 
v___x_2270_ = ((size_t)1ULL);
v___x_2271_ = lean_usize_add(v_i_2259_, v___x_2270_);
v_i_2259_ = v___x_2271_;
v_b_2260_ = v_snd_2269_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33___boxed(lean_object* v_as_2318_, lean_object* v_sz_2319_, lean_object* v_i_2320_, lean_object* v_b_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
size_t v_sz_boxed_2329_; size_t v_i_boxed_2330_; lean_object* v_res_2331_; 
v_sz_boxed_2329_ = lean_unbox_usize(v_sz_2319_);
lean_dec(v_sz_2319_);
v_i_boxed_2330_ = lean_unbox_usize(v_i_2320_);
lean_dec(v_i_2320_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(v_as_2318_, v_sz_boxed_2329_, v_i_boxed_2330_, v_b_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v_as_2318_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(lean_object* v_attrInstances_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_attrs_2342_; size_t v_sz_2343_; size_t v___x_2344_; lean_object* v___x_2345_; 
v_attrs_2342_ = ((lean_object*)(l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___closed__0));
v_sz_2343_ = lean_array_size(v_attrInstances_2334_);
v___x_2344_ = ((size_t)0ULL);
v___x_2345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__33(v_attrInstances_2334_, v_sz_2343_, v___x_2344_, v_attrs_2342_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___boxed(lean_object* v_attrInstances_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(v_attrInstances_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_attrInstances_2346_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(lean_object* v_stx_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = l_Lean_Syntax_getArg(v_stx_2355_, v___x_2363_);
v___x_2365_ = l_Lean_Syntax_getSepArgs(v___x_2364_);
lean_dec(v___x_2364_);
v___x_2366_ = l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22(v___x_2365_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec_ref(v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9___boxed(lean_object* v_stx_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(v_stx_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v_stx_2367_);
return v_res_2375_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__0));
v___x_2378_ = l_Lean_stringToMessageData(v___x_2377_);
return v___x_2378_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__2));
v___x_2381_ = l_Lean_stringToMessageData(v___x_2380_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__4));
v___x_2384_ = l_Lean_stringToMessageData(v___x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5(lean_object* v_addInfo_2385_, lean_object* v_declName_2386_, uint8_t v___x_2387_, lean_object* v___f_2388_, uint8_t v___x_2389_, lean_object* v_env_2390_, lean_object* v___f_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v___x_2399_; 
lean_inc(v___y_2397_);
lean_inc_ref(v___y_2396_);
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
lean_inc(v___y_2393_);
lean_inc_ref(v___y_2392_);
lean_inc(v_declName_2386_);
v___x_2399_ = lean_apply_8(v_addInfo_2385_, v_declName_2386_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, lean_box(0));
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v___x_2400_; 
lean_dec_ref(v___x_2399_);
lean_inc(v_declName_2386_);
v___x_2400_ = lean_private_to_user_name(v_declName_2386_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2401_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2402_ = l_Lean_MessageData_ofConstName(v_declName_2386_, v___x_2387_);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2405_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v___x_2406_;
}
else
{
lean_object* v_val_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec(v_declName_2386_);
v_val_2407_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_val_2407_);
lean_dec_ref(v___x_2400_);
v___x_2408_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__5);
v___x_2409_ = l_Lean_MessageData_ofConstName(v_val_2407_, v___x_2387_);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2412_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v___x_2413_;
}
}
else
{
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v_declName_2386_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___boxed(lean_object* v_addInfo_2414_, lean_object* v_declName_2415_, lean_object* v___x_2416_, lean_object* v___f_2417_, lean_object* v___x_2418_, lean_object* v_env_2419_, lean_object* v___f_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
uint8_t v___x_54919__boxed_2428_; uint8_t v___x_54921__boxed_2429_; lean_object* v_res_2430_; 
v___x_54919__boxed_2428_ = lean_unbox(v___x_2416_);
v___x_54921__boxed_2429_ = lean_unbox(v___x_2418_);
v_res_2430_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5(v_addInfo_2414_, v_declName_2415_, v___x_54919__boxed_2428_, v___f_2417_, v___x_54921__boxed_2429_, v_env_2419_, v___f_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec_ref(v___f_2420_);
lean_dec_ref(v_env_2419_);
lean_dec_ref(v___f_2417_);
return v_res_2430_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__0));
v___x_2433_ = l_Lean_stringToMessageData(v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3(lean_object* v___f_2434_, lean_object* v_declName_2435_, uint8_t v___x_2436_, lean_object* v_env_2437_, lean_object* v_____do__lift_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v___y_2447_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
lean_inc(v_declName_2435_);
v___x_2456_ = l_Lean_privateToUserName(v_declName_2435_);
lean_inc_ref(v_env_2437_);
v___x_2457_ = lean_is_reserved_name(v_env_2437_, v___x_2456_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
lean_inc(v_declName_2435_);
v___x_2458_ = l_Lean_mkPrivateName(v_____do__lift_2438_, v_declName_2435_);
v___x_2459_ = lean_is_reserved_name(v_env_2437_, v___x_2458_);
v___y_2447_ = v___x_2459_;
goto v___jp_2446_;
}
else
{
lean_dec_ref(v_env_2437_);
v___y_2447_ = v___x_2457_;
goto v___jp_2446_;
}
v___jp_2446_:
{
if (v___y_2447_ == 0)
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_dec(v_declName_2435_);
v___x_2448_ = lean_box(0);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2441_);
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
v___x_2449_ = lean_apply_8(v___f_2434_, v___x_2448_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, lean_box(0));
return v___x_2449_;
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
lean_dec_ref(v___f_2434_);
v___x_2450_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2451_ = l_Lean_MessageData_ofConstName(v_declName_2435_, v___x_2436_);
v___x_2452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___closed__1);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2454_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___boxed(lean_object* v___f_2460_, lean_object* v_declName_2461_, lean_object* v___x_2462_, lean_object* v_env_2463_, lean_object* v_____do__lift_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
uint8_t v___x_55007__boxed_2472_; lean_object* v_res_2473_; 
v___x_55007__boxed_2472_ = lean_unbox(v___x_2462_);
v_res_2473_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3(v___f_2460_, v_declName_2461_, v___x_55007__boxed_2472_, v_env_2463_, v_____do__lift_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec_ref(v_____do__lift_2464_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(lean_object* v_t_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v_infoState_2478_; uint8_t v_enabled_2479_; 
v___x_2477_ = lean_st_ref_get(v___y_2475_);
v_infoState_2478_ = lean_ctor_get(v___x_2477_, 7);
lean_inc_ref(v_infoState_2478_);
lean_dec(v___x_2477_);
v_enabled_2479_ = lean_ctor_get_uint8(v_infoState_2478_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2478_);
if (v_enabled_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec_ref(v_t_2474_);
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
return v___x_2481_;
}
else
{
lean_object* v___x_2482_; lean_object* v_infoState_2483_; lean_object* v_env_2484_; lean_object* v_nextMacroScope_2485_; lean_object* v_ngen_2486_; lean_object* v_auxDeclNGen_2487_; lean_object* v_traceState_2488_; lean_object* v_cache_2489_; lean_object* v_messages_2490_; lean_object* v_snapshotTasks_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2513_; 
v___x_2482_ = lean_st_ref_take(v___y_2475_);
v_infoState_2483_ = lean_ctor_get(v___x_2482_, 7);
v_env_2484_ = lean_ctor_get(v___x_2482_, 0);
v_nextMacroScope_2485_ = lean_ctor_get(v___x_2482_, 1);
v_ngen_2486_ = lean_ctor_get(v___x_2482_, 2);
v_auxDeclNGen_2487_ = lean_ctor_get(v___x_2482_, 3);
v_traceState_2488_ = lean_ctor_get(v___x_2482_, 4);
v_cache_2489_ = lean_ctor_get(v___x_2482_, 5);
v_messages_2490_ = lean_ctor_get(v___x_2482_, 6);
v_snapshotTasks_2491_ = lean_ctor_get(v___x_2482_, 8);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2493_ = v___x_2482_;
v_isShared_2494_ = v_isSharedCheck_2513_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_snapshotTasks_2491_);
lean_inc(v_infoState_2483_);
lean_inc(v_messages_2490_);
lean_inc(v_cache_2489_);
lean_inc(v_traceState_2488_);
lean_inc(v_auxDeclNGen_2487_);
lean_inc(v_ngen_2486_);
lean_inc(v_nextMacroScope_2485_);
lean_inc(v_env_2484_);
lean_dec(v___x_2482_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2513_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
uint8_t v_enabled_2495_; lean_object* v_assignment_2496_; lean_object* v_lazyAssignment_2497_; lean_object* v_trees_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2512_; 
v_enabled_2495_ = lean_ctor_get_uint8(v_infoState_2483_, sizeof(void*)*3);
v_assignment_2496_ = lean_ctor_get(v_infoState_2483_, 0);
v_lazyAssignment_2497_ = lean_ctor_get(v_infoState_2483_, 1);
v_trees_2498_ = lean_ctor_get(v_infoState_2483_, 2);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_infoState_2483_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2500_ = v_infoState_2483_;
v_isShared_2501_ = v_isSharedCheck_2512_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_trees_2498_);
lean_inc(v_lazyAssignment_2497_);
lean_inc(v_assignment_2496_);
lean_dec(v_infoState_2483_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2512_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
v___x_2502_ = l_Lean_PersistentArray_push___redArg(v_trees_2498_, v_t_2474_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 2, v___x_2502_);
v___x_2504_ = v___x_2500_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_assignment_2496_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_lazyAssignment_2497_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v___x_2502_);
lean_ctor_set_uint8(v_reuseFailAlloc_2511_, sizeof(void*)*3, v_enabled_2495_);
v___x_2504_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
lean_object* v___x_2506_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 7, v___x_2504_);
v___x_2506_ = v___x_2493_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_env_2484_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_nextMacroScope_2485_);
lean_ctor_set(v_reuseFailAlloc_2510_, 2, v_ngen_2486_);
lean_ctor_set(v_reuseFailAlloc_2510_, 3, v_auxDeclNGen_2487_);
lean_ctor_set(v_reuseFailAlloc_2510_, 4, v_traceState_2488_);
lean_ctor_set(v_reuseFailAlloc_2510_, 5, v_cache_2489_);
lean_ctor_set(v_reuseFailAlloc_2510_, 6, v_messages_2490_);
lean_ctor_set(v_reuseFailAlloc_2510_, 7, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2510_, 8, v_snapshotTasks_2491_);
v___x_2506_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = lean_st_ref_set(v___y_2475_, v___x_2506_);
v___x_2508_ = lean_box(0);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_t_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v_t_2514_, v___y_2515_);
lean_dec(v___y_2515_);
return v_res_2517_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = lean_unsigned_to_nat(32u);
v___x_2519_ = lean_mk_empty_array_with_capacity(v___x_2518_);
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1(void){
_start:
{
size_t v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2521_ = ((size_t)5ULL);
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_unsigned_to_nat(32u);
v___x_2524_ = lean_mk_empty_array_with_capacity(v___x_2523_);
v___x_2525_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__0);
v___x_2526_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
lean_ctor_set(v___x_2526_, 1, v___x_2524_);
lean_ctor_set(v___x_2526_, 2, v___x_2522_);
lean_ctor_set(v___x_2526_, 3, v___x_2522_);
lean_ctor_set_usize(v___x_2526_, 4, v___x_2521_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(lean_object* v_t_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; lean_object* v_infoState_2536_; uint8_t v_enabled_2537_; 
v___x_2535_ = lean_st_ref_get(v___y_2533_);
v_infoState_2536_ = lean_ctor_get(v___x_2535_, 7);
lean_inc_ref(v_infoState_2536_);
lean_dec(v___x_2535_);
v_enabled_2537_ = lean_ctor_get_uint8(v_infoState_2536_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2536_);
if (v_enabled_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref(v_t_2527_);
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
return v___x_2539_;
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2540_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___closed__1);
v___x_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2541_, 0, v_t_2527_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v___x_2541_, v___y_2533_);
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2___boxed(lean_object* v_t_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(v_t_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__4(lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
if (lean_obj_tag(v_a_2552_) == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = l_List_reverse___redArg(v_a_2553_);
return v___x_2554_;
}
else
{
lean_object* v_head_2555_; lean_object* v_tail_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2565_; 
v_head_2555_ = lean_ctor_get(v_a_2552_, 0);
v_tail_2556_ = lean_ctor_get(v_a_2552_, 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_a_2552_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2558_ = v_a_2552_;
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_tail_2556_);
lean_inc(v_head_2555_);
lean_dec(v_a_2552_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2565_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2560_ = l_Lean_mkLevelParam(v_head_2555_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v_a_2553_);
lean_ctor_set(v___x_2558_, 0, v___x_2560_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v_a_2553_);
v___x_2562_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
v_a_2552_ = v_tail_2556_;
v_a_2553_ = v___x_2562_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0(void){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2566_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__0);
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
return v___x_2568_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
lean_ctor_set(v___x_2571_, 2, v___x_2570_);
lean_ctor_set(v___x_2571_, 3, v___x_2570_);
lean_ctor_set(v___x_2571_, 4, v___x_2569_);
lean_ctor_set(v___x_2571_, 5, v___x_2569_);
lean_ctor_set(v___x_2571_, 6, v___x_2569_);
lean_ctor_set(v___x_2571_, 7, v___x_2569_);
lean_ctor_set(v___x_2571_, 8, v___x_2569_);
lean_ctor_set(v___x_2571_, 9, v___x_2569_);
return v___x_2571_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = lean_unsigned_to_nat(32u);
v___x_2573_ = lean_mk_empty_array_with_capacity(v___x_2572_);
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
return v___x_2574_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4(void){
_start:
{
size_t v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2575_ = ((size_t)5ULL);
v___x_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_unsigned_to_nat(32u);
v___x_2578_ = lean_mk_empty_array_with_capacity(v___x_2577_);
v___x_2579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__3);
v___x_2580_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2578_);
lean_ctor_set(v___x_2580_, 2, v___x_2576_);
lean_ctor_set(v___x_2580_, 3, v___x_2576_);
lean_ctor_set_usize(v___x_2580_, 4, v___x_2575_);
return v___x_2580_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2581_ = lean_box(1);
v___x_2582_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4);
v___x_2583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__1);
v___x_2584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v___x_2582_);
lean_ctor_set(v___x_2584_, 2, v___x_2581_);
return v___x_2584_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__6));
v___x_2587_ = l_Lean_stringToMessageData(v___x_2586_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__8));
v___x_2590_ = l_Lean_stringToMessageData(v___x_2589_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__10));
v___x_2593_ = l_Lean_stringToMessageData(v___x_2592_);
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__12));
v___x_2596_ = l_Lean_stringToMessageData(v___x_2595_);
return v___x_2596_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__14));
v___x_2599_ = l_Lean_stringToMessageData(v___x_2598_);
return v___x_2599_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__16));
v___x_2602_ = l_Lean_stringToMessageData(v___x_2601_);
return v___x_2602_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__19(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__18));
v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(lean_object* v_msg_2606_, lean_object* v_declHint_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; lean_object* v_env_2611_; uint8_t v___x_2612_; 
v___x_2610_ = lean_st_ref_get(v___y_2608_);
v_env_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc_ref(v_env_2611_);
lean_dec(v___x_2610_);
v___x_2612_ = l_Lean_Name_isAnonymous(v_declHint_2607_);
if (v___x_2612_ == 0)
{
uint8_t v_isExporting_2613_; 
v_isExporting_2613_ = lean_ctor_get_uint8(v_env_2611_, sizeof(void*)*8);
if (v_isExporting_2613_ == 0)
{
lean_object* v___x_2614_; 
lean_dec_ref(v_env_2611_);
lean_dec(v_declHint_2607_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v_msg_2606_);
return v___x_2614_;
}
else
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
lean_inc_ref(v_env_2611_);
v___x_2615_ = l_Lean_Environment_setExporting(v_env_2611_, v___x_2612_);
lean_inc(v_declHint_2607_);
lean_inc_ref(v___x_2615_);
v___x_2616_ = l_Lean_Environment_contains(v___x_2615_, v_declHint_2607_, v_isExporting_2613_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_env_2611_);
lean_dec(v_declHint_2607_);
v___x_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2617_, 0, v_msg_2606_);
return v___x_2617_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v_c_2623_; lean_object* v___x_2624_; 
v___x_2618_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__2);
v___x_2619_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__5);
v___x_2620_ = l_Lean_Options_empty;
v___x_2621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2615_);
lean_ctor_set(v___x_2621_, 1, v___x_2618_);
lean_ctor_set(v___x_2621_, 2, v___x_2619_);
lean_ctor_set(v___x_2621_, 3, v___x_2620_);
lean_inc(v_declHint_2607_);
v___x_2622_ = l_Lean_MessageData_ofConstName(v_declHint_2607_, v___x_2612_);
v_c_2623_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2623_, 0, v___x_2621_);
lean_ctor_set(v_c_2623_, 1, v___x_2622_);
v___x_2624_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2611_, v_declHint_2607_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec_ref(v_env_2611_);
lean_dec(v_declHint_2607_);
v___x_2625_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7);
v___x_2626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
lean_ctor_set(v___x_2626_, 1, v_c_2623_);
v___x_2627_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__9);
v___x_2628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2626_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = l_Lean_MessageData_note(v___x_2628_);
v___x_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2630_, 0, v_msg_2606_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
return v___x_2631_;
}
else
{
lean_object* v_val_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2667_; 
v_val_2632_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2634_ = v___x_2624_;
v_isShared_2635_ = v_isSharedCheck_2667_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_val_2632_);
lean_dec(v___x_2624_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2667_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v_mod_2639_; uint8_t v___x_2640_; 
v___x_2636_ = lean_box(0);
v___x_2637_ = l_Lean_Environment_header(v_env_2611_);
lean_dec_ref(v_env_2611_);
v___x_2638_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2637_);
v_mod_2639_ = lean_array_get(v___x_2636_, v___x_2638_, v_val_2632_);
lean_dec(v_val_2632_);
lean_dec_ref(v___x_2638_);
v___x_2640_ = l_Lean_isPrivateName(v_declHint_2607_);
lean_dec(v_declHint_2607_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__11);
v___x_2642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
lean_ctor_set(v___x_2642_, 1, v_c_2623_);
v___x_2643_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__13);
v___x_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = l_Lean_MessageData_ofName(v_mod_2639_);
v___x_2646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2644_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
v___x_2647_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__15);
v___x_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2646_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_MessageData_note(v___x_2648_);
v___x_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2650_, 0, v_msg_2606_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2650_);
v___x_2652_ = v___x_2634_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__7);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
lean_ctor_set(v___x_2655_, 1, v_c_2623_);
v___x_2656_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__17);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_MessageData_ofName(v_mod_2639_);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__19);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_MessageData_note(v___x_2661_);
v___x_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2663_, 0, v_msg_2606_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2663_);
v___x_2665_ = v___x_2634_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2668_; 
lean_dec_ref(v_env_2611_);
lean_dec(v_declHint_2607_);
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_msg_2606_);
return v___x_2668_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___boxed(lean_object* v_msg_2669_, lean_object* v_declHint_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(v_msg_2669_, v_declHint_2670_, v___y_2671_);
lean_dec(v___y_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(lean_object* v_msg_2674_, lean_object* v_declHint_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2693_; 
v___x_2683_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(v_msg_2674_, v_declHint_2675_, v___y_2681_);
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2693_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2688_ = l_Lean_unknownIdentifierMessageTag;
v___x_2689_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
lean_ctor_set(v___x_2689_, 1, v_a_2684_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2689_);
v___x_2691_ = v___x_2686_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44___boxed(lean_object* v_msg_2694_, lean_object* v_declHint_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(v_msg_2694_, v_declHint_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(lean_object* v_ref_2704_, lean_object* v_msg_2705_, lean_object* v_declHint_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; lean_object* v_a_2715_; lean_object* v___x_2716_; 
v___x_2714_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44(v_msg_2705_, v_declHint_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref(v___x_2714_);
v___x_2716_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v_ref_2704_, v_a_2715_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg___boxed(lean_object* v_ref_2717_, lean_object* v_msg_2718_, lean_object* v_declHint_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(v_ref_2717_, v_msg_2718_, v_declHint_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v_ref_2717_);
return v_res_2727_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2729_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__0));
v___x_2730_ = l_Lean_stringToMessageData(v___x_2729_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(lean_object* v_ref_2731_, lean_object* v_constName_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2740_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___closed__1);
v___x_2741_ = 0;
lean_inc(v_constName_2732_);
v___x_2742_ = l_Lean_MessageData_ofConstName(v_constName_2732_, v___x_2741_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2740_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(v_ref_2731_, v___x_2745_, v_constName_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg___boxed(lean_object* v_ref_2747_, lean_object* v_constName_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(v_ref_2747_, v_constName_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v_ref_2747_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(lean_object* v_constName_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_ref_2765_; lean_object* v___x_2766_; 
v_ref_2765_ = lean_ctor_get(v___y_2762_, 5);
v___x_2766_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(v_ref_2765_, v_constName_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg___boxed(lean_object* v_constName_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(v_constName_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(lean_object* v_constName_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; lean_object* v_env_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; 
v___x_2784_ = lean_st_ref_get(v___y_2782_);
v_env_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc_ref(v_env_2785_);
lean_dec(v___x_2784_);
v___x_2786_ = 0;
lean_inc(v_constName_2776_);
v___x_2787_ = l_Lean_Environment_findConstVal_x3f(v_env_2785_, v_constName_2776_, v___x_2786_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(v_constName_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v___x_2788_;
}
else
{
lean_object* v_val_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec(v_constName_2776_);
v_val_2789_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2787_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_val_2789_);
lean_dec(v___x_2787_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 0);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_val_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3___boxed(lean_object* v_constName_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(v_constName_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(lean_object* v_constName_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; 
lean_inc(v_constName_2806_);
v___x_2814_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3(v_constName_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2826_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2826_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2826_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_levelParams_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
v_levelParams_2819_ = lean_ctor_get(v_a_2815_, 1);
lean_inc(v_levelParams_2819_);
lean_dec(v_a_2815_);
v___x_2820_ = lean_box(0);
v___x_2821_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__4(v_levelParams_2819_, v___x_2820_);
v___x_2822_ = l_Lean_mkConst(v_constName_2806_, v___x_2821_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2822_);
v___x_2824_ = v___x_2817_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_constName_2806_);
v_a_2827_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2814_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2814_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1___boxed(lean_object* v_constName_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(v_constName_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2843_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2844_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__0);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2847_ = lean_box(1);
v___x_2848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg___closed__4);
v___x_2849_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__1);
v___x_2850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2848_);
lean_ctor_set(v___x_2850_, 2, v___x_2847_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0(uint8_t v___x_2851_, lean_object* v_declName_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_ref_2860_; lean_object* v___x_2861_; 
v_ref_2860_ = lean_ctor_get(v___y_2857_, 5);
v___x_2861_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1(v_declName_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = lean_box(0);
lean_inc(v_ref_2860_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v_ref_2860_);
v___x_2865_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___closed__2);
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2867_, 0, v___x_2864_);
lean_ctor_set(v___x_2867_, 1, v___x_2865_);
lean_ctor_set(v___x_2867_, 2, v___x_2866_);
lean_ctor_set(v___x_2867_, 3, v_a_2862_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*4, v___x_2851_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*4 + 1, v___x_2851_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
v___x_2869_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2(v___x_2868_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
return v___x_2869_;
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
v_a_2870_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2861_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2861_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0___boxed(lean_object* v___x_2878_, lean_object* v_declName_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
uint8_t v___x_55738__boxed_2887_; lean_object* v_res_2888_; 
v___x_55738__boxed_2887_ = lean_unbox(v___x_2878_);
v_res_2888_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__0(v___x_55738__boxed_2887_, v_declName_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2888_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__0));
v___x_2891_ = l_Lean_stringToMessageData(v___x_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2(lean_object* v_env_2892_, lean_object* v_declName_2893_, lean_object* v___f_2894_, lean_object* v_addInfo_2895_, lean_object* v_____r_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; uint8_t v___x_2905_; uint8_t v___x_2906_; 
lean_inc(v_declName_2893_);
v___x_2904_ = l_Lean_mkPrivateName(v_env_2892_, v_declName_2893_);
v___x_2905_ = 1;
lean_inc(v___x_2904_);
v___x_2906_ = l_Lean_Environment_contains(v_env_2892_, v___x_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec(v___x_2904_);
lean_dec_ref(v_addInfo_2895_);
lean_dec(v_declName_2893_);
v___x_2907_ = lean_box(0);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v___y_2900_);
lean_inc_ref(v___y_2899_);
lean_inc(v___y_2898_);
lean_inc_ref(v___y_2897_);
v___x_2908_ = lean_apply_8(v___f_2894_, v___x_2907_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, lean_box(0));
return v___x_2908_;
}
else
{
lean_object* v___x_2909_; 
lean_dec_ref(v___f_2894_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc(v___y_2900_);
lean_inc_ref(v___y_2899_);
lean_inc(v___y_2898_);
lean_inc_ref(v___y_2897_);
v___x_2909_ = lean_apply_8(v_addInfo_2895_, v___x_2904_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, lean_box(0));
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_dec_ref(v___x_2909_);
v___x_2910_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___closed__1);
v___x_2911_ = l_Lean_MessageData_ofConstName(v_declName_2893_, v___x_2905_);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2914_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
return v___x_2915_;
}
else
{
lean_dec(v_declName_2893_);
return v___x_2909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___boxed(lean_object* v_env_2916_, lean_object* v_declName_2917_, lean_object* v___f_2918_, lean_object* v_addInfo_2919_, lean_object* v_____r_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2(v_env_2916_, v_declName_2917_, v___f_2918_, v_addInfo_2919_, v_____r_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4(lean_object* v___f_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v___x_2937_; lean_object* v_env_2938_; lean_object* v___x_2939_; 
v___x_2937_ = lean_st_ref_get(v___y_2935_);
v_env_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc_ref(v_env_2938_);
lean_dec(v___x_2937_);
v___x_2939_ = lean_apply_8(v___f_2929_, v_env_2938_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, lean_box(0));
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4___boxed(lean_object* v___f_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4(v___f_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
return v_res_2948_;
}
}
static lean_object* _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__0));
v___x_2951_ = l_Lean_stringToMessageData(v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1(lean_object* v_declName_2952_, lean_object* v_env_2953_, lean_object* v_addInfo_2954_, lean_object* v_____r_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_private_to_user_name(v_declName_2952_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref(v_addInfo_2954_);
lean_dec_ref(v_env_2953_);
v___x_2964_ = lean_box(0);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
else
{
lean_object* v_val_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2983_; 
v_val_2966_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2968_ = v___x_2963_;
v_isShared_2969_ = v_isSharedCheck_2983_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_val_2966_);
lean_dec(v___x_2963_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2983_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
uint8_t v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = 1;
lean_inc(v_val_2966_);
v___x_2971_ = l_Lean_Environment_contains(v_env_2953_, v_val_2966_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_val_2966_);
lean_dec_ref(v_addInfo_2954_);
v___x_2972_ = lean_box(0);
if (v_isShared_2969_ == 0)
{
lean_ctor_set_tag(v___x_2968_, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2972_);
v___x_2974_ = v___x_2968_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
else
{
lean_object* v___x_2976_; 
lean_del_object(v___x_2968_);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
lean_inc(v___y_2957_);
lean_inc_ref(v___y_2956_);
lean_inc(v_val_2966_);
v___x_2976_ = lean_apply_8(v_addInfo_2954_, v_val_2966_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, lean_box(0));
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_dec_ref(v___x_2976_);
v___x_2977_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___closed__1);
v___x_2978_ = l_Lean_MessageData_ofConstName(v_val_2966_, v___x_2970_);
v___x_2979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2977_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_2981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2979_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___x_2982_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_2981_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
return v___x_2982_;
}
else
{
lean_dec(v_val_2966_);
return v___x_2976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___boxed(lean_object* v_declName_2984_, lean_object* v_env_2985_, lean_object* v_addInfo_2986_, lean_object* v_____r_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1(v_declName_2984_, v_env_2985_, v_addInfo_2986_, v_____r_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(lean_object* v_env_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v___x_3000_; lean_object* v_nextMacroScope_3001_; lean_object* v_ngen_3002_; lean_object* v_auxDeclNGen_3003_; lean_object* v_traceState_3004_; lean_object* v_messages_3005_; lean_object* v_infoState_3006_; lean_object* v_snapshotTasks_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3033_; 
v___x_3000_ = lean_st_ref_take(v___y_2998_);
v_nextMacroScope_3001_ = lean_ctor_get(v___x_3000_, 1);
v_ngen_3002_ = lean_ctor_get(v___x_3000_, 2);
v_auxDeclNGen_3003_ = lean_ctor_get(v___x_3000_, 3);
v_traceState_3004_ = lean_ctor_get(v___x_3000_, 4);
v_messages_3005_ = lean_ctor_get(v___x_3000_, 6);
v_infoState_3006_ = lean_ctor_get(v___x_3000_, 7);
v_snapshotTasks_3007_ = lean_ctor_get(v___x_3000_, 8);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3033_ == 0)
{
lean_object* v_unused_3034_; lean_object* v_unused_3035_; 
v_unused_3034_ = lean_ctor_get(v___x_3000_, 5);
lean_dec(v_unused_3034_);
v_unused_3035_ = lean_ctor_get(v___x_3000_, 0);
lean_dec(v_unused_3035_);
v___x_3009_ = v___x_3000_;
v_isShared_3010_ = v_isSharedCheck_3033_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_snapshotTasks_3007_);
lean_inc(v_infoState_3006_);
lean_inc(v_messages_3005_);
lean_inc(v_traceState_3004_);
lean_inc(v_auxDeclNGen_3003_);
lean_inc(v_ngen_3002_);
lean_inc(v_nextMacroScope_3001_);
lean_dec(v___x_3000_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3033_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3011_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__2);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 5, v___x_3011_);
lean_ctor_set(v___x_3009_, 0, v_env_2996_);
v___x_3013_ = v___x_3009_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_env_2996_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v_nextMacroScope_3001_);
lean_ctor_set(v_reuseFailAlloc_3032_, 2, v_ngen_3002_);
lean_ctor_set(v_reuseFailAlloc_3032_, 3, v_auxDeclNGen_3003_);
lean_ctor_set(v_reuseFailAlloc_3032_, 4, v_traceState_3004_);
lean_ctor_set(v_reuseFailAlloc_3032_, 5, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3032_, 6, v_messages_3005_);
lean_ctor_set(v_reuseFailAlloc_3032_, 7, v_infoState_3006_);
lean_ctor_set(v_reuseFailAlloc_3032_, 8, v_snapshotTasks_3007_);
v___x_3013_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v_mctx_3016_; lean_object* v_zetaDeltaFVarIds_3017_; lean_object* v_postponed_3018_; lean_object* v_diag_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3030_; 
v___x_3014_ = lean_st_ref_set(v___y_2998_, v___x_3013_);
v___x_3015_ = lean_st_ref_take(v___y_2997_);
v_mctx_3016_ = lean_ctor_get(v___x_3015_, 0);
v_zetaDeltaFVarIds_3017_ = lean_ctor_get(v___x_3015_, 2);
v_postponed_3018_ = lean_ctor_get(v___x_3015_, 3);
v_diag_3019_ = lean_ctor_get(v___x_3015_, 4);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; 
v_unused_3031_ = lean_ctor_get(v___x_3015_, 1);
lean_dec(v_unused_3031_);
v___x_3021_ = v___x_3015_;
v_isShared_3022_ = v_isSharedCheck_3030_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_diag_3019_);
lean_inc(v_postponed_3018_);
lean_inc(v_zetaDeltaFVarIds_3017_);
lean_inc(v_mctx_3016_);
lean_dec(v___x_3015_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3030_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = lean_obj_once(&l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3, &l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3_once, _init_l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg___closed__3);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_mctx_3016_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3029_, 2, v_zetaDeltaFVarIds_3017_);
lean_ctor_set(v_reuseFailAlloc_3029_, 3, v_postponed_3018_);
lean_ctor_set(v_reuseFailAlloc_3029_, 4, v_diag_3019_);
v___x_3025_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = lean_st_ref_set(v___y_2997_, v___x_3025_);
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
return v___x_3028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_env_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec(v___y_3037_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(lean_object* v_env_3041_, lean_object* v_x_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v_env_3051_; lean_object* v_a_3053_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3050_ = lean_st_ref_get(v___y_3048_);
v_env_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc_ref(v_env_3051_);
lean_dec(v___x_3050_);
v___x_3063_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3041_, v___y_3046_, v___y_3048_);
lean_dec_ref(v___x_3063_);
lean_inc(v___y_3048_);
lean_inc_ref(v___y_3047_);
lean_inc(v___y_3046_);
lean_inc_ref(v___y_3045_);
lean_inc(v___y_3044_);
lean_inc_ref(v___y_3043_);
v___x_3064_ = lean_apply_7(v_x_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, lean_box(0));
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref(v___x_3064_);
v___x_3066_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3051_, v___y_3046_, v___y_3048_);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v___x_3066_, 0);
lean_dec(v_unused_3074_);
v___x_3068_ = v___x_3066_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_dec(v___x_3066_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v_a_3065_);
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3065_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
else
{
lean_object* v_a_3075_; 
v_a_3075_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3075_);
lean_dec_ref(v___x_3064_);
v_a_3053_ = v_a_3075_;
goto v___jp_3052_;
}
v___jp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
v___x_3054_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3051_, v___y_3046_, v___y_3048_);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; 
v_unused_3062_ = lean_ctor_get(v___x_3054_, 0);
lean_dec(v_unused_3062_);
v___x_3056_ = v___x_3054_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_dec(v___x_3054_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set_tag(v___x_3056_, 1);
lean_ctor_set(v___x_3056_, 0, v_a_3053_);
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3053_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg___boxed(lean_object* v_env_3076_, lean_object* v_x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3076_, v_x_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(lean_object* v_declName_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___x_3097_; lean_object* v_env_3098_; uint8_t v___x_3099_; lean_object* v_addInfo_3100_; lean_object* v_env_3101_; lean_object* v___f_3102_; lean_object* v___f_3103_; lean_object* v___x_3104_; lean_object* v___f_3105_; uint8_t v___x_3106_; uint8_t v___x_3107_; 
v___x_3097_ = lean_st_ref_get(v___y_3095_);
v_env_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc_ref(v_env_3098_);
lean_dec(v___x_3097_);
v___x_3099_ = 0;
v_addInfo_3100_ = ((lean_object*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___closed__0));
v_env_3101_ = l_Lean_Environment_setExporting(v_env_3098_, v___x_3099_);
lean_inc_ref_n(v_env_3101_, 4);
lean_inc_n(v_declName_3089_, 4);
v___f_3102_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__1___boxed), 11, 3);
lean_closure_set(v___f_3102_, 0, v_declName_3089_);
lean_closure_set(v___f_3102_, 1, v_env_3101_);
lean_closure_set(v___f_3102_, 2, v_addInfo_3100_);
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3103_, 0, v_env_3101_);
lean_closure_set(v___f_3103_, 1, v_declName_3089_);
lean_closure_set(v___f_3103_, 2, v___f_3102_);
lean_closure_set(v___f_3103_, 3, v_addInfo_3100_);
v___x_3104_ = lean_box(v___x_3099_);
lean_inc_ref(v___f_3103_);
v___f_3105_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__3___boxed), 12, 4);
lean_closure_set(v___f_3105_, 0, v___f_3103_);
lean_closure_set(v___f_3105_, 1, v_declName_3089_);
lean_closure_set(v___f_3105_, 2, v___x_3104_);
lean_closure_set(v___f_3105_, 3, v_env_3101_);
v___x_3106_ = 1;
v___x_3107_ = l_Lean_Environment_contains(v_env_3101_, v_declName_3089_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___f_3108_; lean_object* v___x_3109_; 
lean_dec_ref(v___f_3103_);
lean_dec(v_declName_3089_);
v___f_3108_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__4___boxed), 8, 1);
lean_closure_set(v___f_3108_, 0, v___f_3105_);
v___x_3109_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3101_, v___f_3108_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___f_3112_; lean_object* v___x_3113_; 
v___x_3110_ = lean_box(v___x_3106_);
v___x_3111_ = lean_box(v___x_3099_);
lean_inc_ref(v_env_3101_);
v___f_3112_ = lean_alloc_closure((void*)(l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___boxed), 14, 7);
lean_closure_set(v___f_3112_, 0, v_addInfo_3100_);
lean_closure_set(v___f_3112_, 1, v_declName_3089_);
lean_closure_set(v___f_3112_, 2, v___x_3110_);
lean_closure_set(v___f_3112_, 3, v___f_3103_);
lean_closure_set(v___f_3112_, 4, v___x_3111_);
lean_closure_set(v___f_3112_, 5, v_env_3101_);
lean_closure_set(v___f_3112_, 6, v___f_3105_);
v___x_3113_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3101_, v___f_3112_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
return v___x_3113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___boxed(lean_object* v_declName_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(v_declName_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
return v_res_3122_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__1));
v___x_3127_ = l_Lean_MessageData_ofFormat(v___x_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0(lean_object* v___x_3128_, uint8_t v___x_3129_, uint8_t v___x_3130_, lean_object* v_xs_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___x_3139_; 
lean_inc(v___x_3128_);
v___x_3139_ = l_Lean_Elab_Term_elabType(v___x_3128_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3139_);
v___x_3141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___closed__2);
v___x_3142_ = l_Lean_Elab_Term_registerCustomErrorIfMVar___redArg(v_a_3140_, v___x_3128_, v___x_3141_, v___y_3133_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v___x_3143_; lean_object* v_fst_3144_; lean_object* v_snd_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v___x_3142_);
v___x_3143_ = l_Array_unzip___redArg(v_xs_3131_);
v_fst_3144_ = lean_ctor_get(v___x_3143_, 0);
v_snd_3145_ = lean_ctor_get(v___x_3143_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3147_ = v___x_3143_;
v_isShared_3148_ = v_isSharedCheck_3170_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_snd_3145_);
lean_inc(v_fst_3144_);
lean_dec(v___x_3143_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3170_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
uint8_t v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = 1;
v___x_3150_ = l_Lean_Meta_mkForallFVars(v_snd_3145_, v_a_3140_, v___x_3129_, v___x_3130_, v___x_3130_, v___x_3149_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v_snd_3145_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3161_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3161_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3161_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 1, v_fst_3144_);
lean_ctor_set(v___x_3147_, 0, v_a_3151_);
v___x_3156_ = v___x_3147_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3151_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_fst_3144_);
v___x_3156_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3158_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v___x_3156_);
v___x_3158_ = v___x_3153_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_del_object(v___x_3147_);
lean_dec(v_fst_3144_);
v_a_3162_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3150_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3150_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_a_3140_);
v_a_3171_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3142_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3142_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v___x_3128_);
v_a_3179_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3139_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3139_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___boxed(lean_object* v___x_3187_, lean_object* v___x_3188_, lean_object* v___x_3189_, lean_object* v_xs_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
uint8_t v___x_56194__boxed_3198_; uint8_t v___x_56195__boxed_3199_; lean_object* v_res_3200_; 
v___x_56194__boxed_3198_ = lean_unbox(v___x_3188_);
v___x_56195__boxed_3199_ = lean_unbox(v___x_3189_);
v_res_3200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0(v___x_3187_, v___x_56194__boxed_3198_, v___x_56195__boxed_3199_, v_xs_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec_ref(v_xs_3190_);
return v_res_3200_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(lean_object* v_declName_3201_, lean_object* v_as_3202_, size_t v_i_3203_, size_t v_stop_3204_){
_start:
{
uint8_t v___x_3205_; 
v___x_3205_ = lean_usize_dec_eq(v_i_3203_, v_stop_3204_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; lean_object* v_declName_3207_; uint8_t v___x_3208_; 
v___x_3206_ = lean_array_uget_borrowed(v_as_3202_, v_i_3203_);
v_declName_3207_ = lean_ctor_get(v___x_3206_, 3);
v___x_3208_ = lean_name_eq(v_declName_3207_, v_declName_3201_);
if (v___x_3208_ == 0)
{
size_t v___x_3209_; size_t v___x_3210_; 
v___x_3209_ = ((size_t)1ULL);
v___x_3210_ = lean_usize_add(v_i_3203_, v___x_3209_);
v_i_3203_ = v___x_3210_;
goto _start;
}
else
{
return v___x_3208_;
}
}
else
{
uint8_t v___x_3212_; 
v___x_3212_ = 0;
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6___boxed(lean_object* v_declName_3213_, lean_object* v_as_3214_, lean_object* v_i_3215_, lean_object* v_stop_3216_){
_start:
{
size_t v_i_boxed_3217_; size_t v_stop_boxed_3218_; uint8_t v_res_3219_; lean_object* v_r_3220_; 
v_i_boxed_3217_ = lean_unbox_usize(v_i_3215_);
lean_dec(v_i_3215_);
v_stop_boxed_3218_ = lean_unbox_usize(v_stop_3216_);
lean_dec(v_stop_3216_);
v_res_3219_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(v_declName_3213_, v_as_3214_, v_i_boxed_3217_, v_stop_boxed_3218_);
lean_dec_ref(v_as_3214_);
lean_dec(v_declName_3213_);
v_r_3220_ = lean_box(v_res_3219_);
return v_r_3220_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1(void){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__0));
v___x_3223_ = l_Lean_stringToMessageData(v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__8));
v___x_3244_ = l_Lean_stringToMessageData(v___x_3243_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(uint8_t v___x_3245_, lean_object* v_as_3246_, size_t v_sz_3247_, size_t v_i_3248_, lean_object* v_b_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_a_3258_; uint8_t v___x_3262_; 
v___x_3262_ = lean_usize_dec_lt(v_i_3248_, v_sz_3247_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v_b_3249_);
return v___x_3263_;
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v_a_3266_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v_valStx_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; uint8_t v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; uint8_t v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; uint8_t v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; uint8_t v___y_3410_; uint8_t v___y_3411_; uint8_t v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; uint8_t v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; uint8_t v___y_3454_; lean_object* v_declName_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; uint8_t v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; uint8_t v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; uint8_t v___y_3484_; lean_object* v___y_3485_; uint8_t v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; uint8_t v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; uint8_t v___y_3503_; lean_object* v___y_3504_; uint8_t v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; uint8_t v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; uint8_t v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; uint8_t v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3567_; lean_object* v_attrs_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3604_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3264_ = lean_unsigned_to_nat(0u);
v___x_3265_ = lean_unsigned_to_nat(1u);
v_a_3266_ = lean_array_uget_borrowed(v_as_3246_, v_i_3248_);
v___x_3619_ = l_Lean_Syntax_getArg(v_a_3266_, v___x_3264_);
v___x_3620_ = l_Lean_Syntax_getOptional_x3f(v___x_3619_);
lean_dec(v___x_3619_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v___x_3621_; 
v___x_3621_ = lean_box(0);
v___y_3604_ = v___x_3621_;
goto v___jp_3603_;
}
else
{
lean_object* v_val_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3631_; 
v_val_3622_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3624_ = v___x_3620_;
v_isShared_3625_ = v_isSharedCheck_3631_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_val_3622_);
lean_dec(v___x_3620_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3631_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3626_ = lean_box(v___x_3245_);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v_val_3622_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v___x_3627_);
v___x_3629_ = v___x_3624_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3627_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
v___y_3604_ = v___x_3629_;
goto v___jp_3603_;
}
}
}
v___jp_3267_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3285_ = lean_unsigned_to_nat(3u);
v___x_3286_ = l_Lean_Syntax_getArg(v_a_3266_, v___x_3285_);
v___x_3287_ = l_Lean_Elab_elabTerminationHints___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__3(v___x_3286_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref(v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3289_, 0, v___y_3274_);
lean_ctor_set(v___x_3289_, 1, v___y_3273_);
lean_ctor_set(v___x_3289_, 2, v___y_3277_);
lean_ctor_set(v___x_3289_, 3, v___y_3271_);
lean_ctor_set(v___x_3289_, 4, v___y_3272_);
lean_ctor_set(v___x_3289_, 5, v___y_3275_);
lean_ctor_set(v___x_3289_, 6, v___y_3269_);
lean_ctor_set(v___x_3289_, 7, v___y_3276_);
lean_ctor_set(v___x_3289_, 8, v___y_3270_);
lean_ctor_set(v___x_3289_, 9, v_valStx_3278_);
lean_ctor_set(v___x_3289_, 10, v_a_3288_);
lean_ctor_set(v___x_3289_, 11, v___y_3268_);
v___x_3290_ = lean_array_push(v_b_3249_, v___x_3289_);
v_a_3258_ = v___x_3290_;
goto v___jp_3257_;
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v_valStx_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v_b_3249_);
v_a_3291_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3287_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3287_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
v___jp_3299_:
{
lean_object* v___x_3316_; 
lean_inc(v___y_3303_);
v___x_3316_ = l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1(v___y_3303_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3316_) == 0)
{
uint8_t v___x_3317_; lean_object* v___x_3318_; 
lean_dec_ref(v___x_3316_);
v___x_3317_ = 2;
lean_inc_ref(v___y_3305_);
lean_inc(v___y_3303_);
v___x_3318_ = l_Lean_Elab_Term_applyAttributesAt(v___y_3303_, v___y_3305_, v___x_3317_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v___x_3319_; 
lean_dec_ref(v___x_3318_);
lean_inc(v___y_3303_);
v___x_3319_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2(v___y_3303_, v___y_3302_, v___y_3306_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___f_3326_; lean_object* v___x_3327_; 
lean_dec_ref(v___x_3319_);
v___x_3320_ = l_Lean_Syntax_getArg(v___y_3302_, v___x_3265_);
v___x_3321_ = l_Lean_Syntax_getArgs(v___x_3320_);
v___x_3322_ = l_Lean_Syntax_getArg(v___y_3302_, v___y_3307_);
v___x_3323_ = l_Lean_Elab_Term_expandOptType(v___y_3306_, v___x_3322_);
lean_dec(v___x_3322_);
v___x_3324_ = lean_box(v___y_3300_);
v___x_3325_ = lean_box(v___x_3262_);
v___f_3326_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3326_, 0, v___x_3323_);
lean_closure_set(v___f_3326_, 1, v___x_3324_);
lean_closure_set(v___f_3326_, 2, v___x_3325_);
v___x_3327_ = l_Lean_Elab_Term_elabBindersEx___redArg(v___x_3321_, v___f_3326_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v_fst_3329_; lean_object* v_snd_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref(v___x_3327_);
v_fst_3329_ = lean_ctor_get(v_a_3328_, 0);
lean_inc_n(v_fst_3329_, 2);
v_snd_3330_ = lean_ctor_get(v_a_3328_, 1);
lean_inc(v_snd_3330_);
lean_dec(v_a_3328_);
v___x_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_fst_3329_);
v___x_3332_ = 2;
v___x_3333_ = lean_box(0);
v___x_3334_ = l_Lean_Meta_mkFreshExprMVar(v___x_3331_, v___x_3332_, v___x_3333_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3334_) == 0)
{
if (v___y_3308_ == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = lean_unsigned_to_nat(3u);
v___x_3337_ = l_Lean_Syntax_getArg(v___y_3302_, v___x_3336_);
v___x_3338_ = lean_box(v___x_3262_);
v___x_3339_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAltsIntoMatch___boxed), 5, 3);
lean_closure_set(v___x_3339_, 0, v___y_3302_);
lean_closure_set(v___x_3339_, 1, v___x_3337_);
lean_closure_set(v___x_3339_, 2, v___x_3338_);
v___x_3340_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v___x_3339_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref(v___x_3340_);
v___y_3268_ = v___y_3301_;
v___y_3269_ = v___x_3320_;
v___y_3270_ = v_a_3335_;
v___y_3271_ = v___y_3303_;
v___y_3272_ = v___y_3304_;
v___y_3273_ = v___y_3305_;
v___y_3274_ = v___y_3306_;
v___y_3275_ = v_snd_3330_;
v___y_3276_ = v_fst_3329_;
v___y_3277_ = v___y_3309_;
v_valStx_3278_ = v_a_3341_;
v___y_3279_ = v___y_3310_;
v___y_3280_ = v___y_3311_;
v___y_3281_ = v___y_3312_;
v___y_3282_ = v___y_3313_;
v___y_3283_ = v___y_3314_;
v___y_3284_ = v___y_3315_;
goto v___jp_3267_;
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec(v_a_3335_);
lean_dec(v_snd_3330_);
lean_dec(v_fst_3329_);
lean_dec(v___x_3320_);
lean_dec(v___y_3309_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3301_);
lean_dec_ref(v_b_3249_);
v_a_3342_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3340_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3340_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_a_3350_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3350_);
lean_dec_ref(v___x_3334_);
v___x_3351_ = lean_unsigned_to_nat(4u);
v___x_3352_ = l_Lean_Syntax_getArg(v___y_3302_, v___x_3351_);
lean_dec(v___y_3302_);
v___y_3268_ = v___y_3301_;
v___y_3269_ = v___x_3320_;
v___y_3270_ = v_a_3350_;
v___y_3271_ = v___y_3303_;
v___y_3272_ = v___y_3304_;
v___y_3273_ = v___y_3305_;
v___y_3274_ = v___y_3306_;
v___y_3275_ = v_snd_3330_;
v___y_3276_ = v_fst_3329_;
v___y_3277_ = v___y_3309_;
v_valStx_3278_ = v___x_3352_;
v___y_3279_ = v___y_3310_;
v___y_3280_ = v___y_3311_;
v___y_3281_ = v___y_3312_;
v___y_3282_ = v___y_3313_;
v___y_3283_ = v___y_3314_;
v___y_3284_ = v___y_3315_;
goto v___jp_3267_;
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec(v_snd_3330_);
lean_dec(v_fst_3329_);
lean_dec(v___x_3320_);
lean_dec(v___y_3309_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v_b_3249_);
v_a_3353_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3334_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3334_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v___x_3320_);
lean_dec(v___y_3309_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v_b_3249_);
v_a_3361_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3327_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3327_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec(v___y_3309_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v_b_3249_);
v_a_3369_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3319_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3319_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v___y_3309_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v_b_3249_);
v_a_3377_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3318_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3318_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec(v___y_3309_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v_b_3249_);
v_a_3385_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3316_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3316_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
v___jp_3393_:
{
if (v___y_3411_ == 0)
{
v___y_3300_ = v___y_3394_;
v___y_3301_ = v___y_3395_;
v___y_3302_ = v___y_3396_;
v___y_3303_ = v___y_3397_;
v___y_3304_ = v___y_3406_;
v___y_3305_ = v___y_3398_;
v___y_3306_ = v___y_3399_;
v___y_3307_ = v___y_3408_;
v___y_3308_ = v___y_3410_;
v___y_3309_ = v___y_3409_;
v___y_3310_ = v___y_3405_;
v___y_3311_ = v___y_3407_;
v___y_3312_ = v___y_3402_;
v___y_3313_ = v___y_3403_;
v___y_3314_ = v___y_3401_;
v___y_3315_ = v___y_3400_;
goto v___jp_3299_;
}
else
{
lean_object* v_fileName_3412_; lean_object* v_fileMap_3413_; lean_object* v_options_3414_; lean_object* v_currRecDepth_3415_; lean_object* v_maxRecDepth_3416_; lean_object* v_ref_3417_; lean_object* v_currNamespace_3418_; lean_object* v_openDecls_3419_; lean_object* v_initHeartbeats_3420_; lean_object* v_maxHeartbeats_3421_; lean_object* v_quotContext_3422_; lean_object* v_currMacroScope_3423_; uint8_t v_diag_3424_; lean_object* v_cancelTk_x3f_3425_; uint8_t v_suppressElabErrors_3426_; lean_object* v_inheritedTraceOptions_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v_ref_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_fileName_3412_ = lean_ctor_get(v___y_3401_, 0);
v_fileMap_3413_ = lean_ctor_get(v___y_3401_, 1);
v_options_3414_ = lean_ctor_get(v___y_3401_, 2);
v_currRecDepth_3415_ = lean_ctor_get(v___y_3401_, 3);
v_maxRecDepth_3416_ = lean_ctor_get(v___y_3401_, 4);
v_ref_3417_ = lean_ctor_get(v___y_3401_, 5);
v_currNamespace_3418_ = lean_ctor_get(v___y_3401_, 6);
v_openDecls_3419_ = lean_ctor_get(v___y_3401_, 7);
v_initHeartbeats_3420_ = lean_ctor_get(v___y_3401_, 8);
v_maxHeartbeats_3421_ = lean_ctor_get(v___y_3401_, 9);
v_quotContext_3422_ = lean_ctor_get(v___y_3401_, 10);
v_currMacroScope_3423_ = lean_ctor_get(v___y_3401_, 11);
v_diag_3424_ = lean_ctor_get_uint8(v___y_3401_, sizeof(void*)*14);
v_cancelTk_x3f_3425_ = lean_ctor_get(v___y_3401_, 12);
v_suppressElabErrors_3426_ = lean_ctor_get_uint8(v___y_3401_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3427_ = lean_ctor_get(v___y_3401_, 13);
v___x_3428_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
lean_inc(v___y_3397_);
v___x_3429_ = l_Lean_MessageData_ofConstName(v___y_3397_, v___y_3404_);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3430_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v_ref_3433_ = l_Lean_replaceRef(v___y_3399_, v_ref_3417_);
lean_inc_ref(v_inheritedTraceOptions_3427_);
lean_inc(v_cancelTk_x3f_3425_);
lean_inc(v_currMacroScope_3423_);
lean_inc(v_quotContext_3422_);
lean_inc(v_maxHeartbeats_3421_);
lean_inc(v_initHeartbeats_3420_);
lean_inc(v_openDecls_3419_);
lean_inc(v_currNamespace_3418_);
lean_inc(v_maxRecDepth_3416_);
lean_inc(v_currRecDepth_3415_);
lean_inc_ref(v_options_3414_);
lean_inc_ref(v_fileMap_3413_);
lean_inc_ref(v_fileName_3412_);
v___x_3434_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3434_, 0, v_fileName_3412_);
lean_ctor_set(v___x_3434_, 1, v_fileMap_3413_);
lean_ctor_set(v___x_3434_, 2, v_options_3414_);
lean_ctor_set(v___x_3434_, 3, v_currRecDepth_3415_);
lean_ctor_set(v___x_3434_, 4, v_maxRecDepth_3416_);
lean_ctor_set(v___x_3434_, 5, v_ref_3433_);
lean_ctor_set(v___x_3434_, 6, v_currNamespace_3418_);
lean_ctor_set(v___x_3434_, 7, v_openDecls_3419_);
lean_ctor_set(v___x_3434_, 8, v_initHeartbeats_3420_);
lean_ctor_set(v___x_3434_, 9, v_maxHeartbeats_3421_);
lean_ctor_set(v___x_3434_, 10, v_quotContext_3422_);
lean_ctor_set(v___x_3434_, 11, v_currMacroScope_3423_);
lean_ctor_set(v___x_3434_, 12, v_cancelTk_x3f_3425_);
lean_ctor_set(v___x_3434_, 13, v_inheritedTraceOptions_3427_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*14, v_diag_3424_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*14 + 1, v_suppressElabErrors_3426_);
v___x_3435_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_3432_, v___y_3405_, v___y_3407_, v___y_3402_, v___y_3403_, v___x_3434_, v___y_3400_);
lean_dec_ref(v___x_3434_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_dec_ref(v___x_3435_);
v___y_3300_ = v___y_3394_;
v___y_3301_ = v___y_3395_;
v___y_3302_ = v___y_3396_;
v___y_3303_ = v___y_3397_;
v___y_3304_ = v___y_3406_;
v___y_3305_ = v___y_3398_;
v___y_3306_ = v___y_3399_;
v___y_3307_ = v___y_3408_;
v___y_3308_ = v___y_3410_;
v___y_3309_ = v___y_3409_;
v___y_3310_ = v___y_3405_;
v___y_3311_ = v___y_3407_;
v___y_3312_ = v___y_3402_;
v___y_3313_ = v___y_3403_;
v___y_3314_ = v___y_3401_;
v___y_3315_ = v___y_3400_;
goto v___jp_3299_;
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec(v___y_3409_);
lean_dec(v___y_3406_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v_b_3249_);
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
v___jp_3444_:
{
lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3462_ = lean_array_get_size(v_b_3249_);
v___x_3463_ = lean_nat_dec_lt(v___x_3264_, v___x_3462_);
if (v___x_3463_ == 0)
{
v___y_3394_ = v___y_3445_;
v___y_3395_ = v___y_3446_;
v___y_3396_ = v___y_3447_;
v___y_3397_ = v_declName_3455_;
v___y_3398_ = v___y_3449_;
v___y_3399_ = v___y_3451_;
v___y_3400_ = v___y_3461_;
v___y_3401_ = v___y_3460_;
v___y_3402_ = v___y_3458_;
v___y_3403_ = v___y_3459_;
v___y_3404_ = v___y_3448_;
v___y_3405_ = v___y_3456_;
v___y_3406_ = v___y_3450_;
v___y_3407_ = v___y_3457_;
v___y_3408_ = v___y_3452_;
v___y_3409_ = v___y_3453_;
v___y_3410_ = v___y_3454_;
v___y_3411_ = v___y_3448_;
goto v___jp_3393_;
}
else
{
if (v___x_3463_ == 0)
{
v___y_3394_ = v___y_3445_;
v___y_3395_ = v___y_3446_;
v___y_3396_ = v___y_3447_;
v___y_3397_ = v_declName_3455_;
v___y_3398_ = v___y_3449_;
v___y_3399_ = v___y_3451_;
v___y_3400_ = v___y_3461_;
v___y_3401_ = v___y_3460_;
v___y_3402_ = v___y_3458_;
v___y_3403_ = v___y_3459_;
v___y_3404_ = v___y_3448_;
v___y_3405_ = v___y_3456_;
v___y_3406_ = v___y_3450_;
v___y_3407_ = v___y_3457_;
v___y_3408_ = v___y_3452_;
v___y_3409_ = v___y_3453_;
v___y_3410_ = v___y_3454_;
v___y_3411_ = v___y_3448_;
goto v___jp_3393_;
}
else
{
size_t v___x_3464_; size_t v___x_3465_; uint8_t v___x_3466_; 
v___x_3464_ = ((size_t)0ULL);
v___x_3465_ = lean_usize_of_nat(v___x_3462_);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__6(v_declName_3455_, v_b_3249_, v___x_3464_, v___x_3465_);
v___y_3394_ = v___y_3445_;
v___y_3395_ = v___y_3446_;
v___y_3396_ = v___y_3447_;
v___y_3397_ = v_declName_3455_;
v___y_3398_ = v___y_3449_;
v___y_3399_ = v___y_3451_;
v___y_3400_ = v___y_3461_;
v___y_3401_ = v___y_3460_;
v___y_3402_ = v___y_3458_;
v___y_3403_ = v___y_3459_;
v___y_3404_ = v___y_3448_;
v___y_3405_ = v___y_3456_;
v___y_3406_ = v___y_3450_;
v___y_3407_ = v___y_3457_;
v___y_3408_ = v___y_3452_;
v___y_3409_ = v___y_3453_;
v___y_3410_ = v___y_3454_;
v___y_3411_ = v___x_3466_;
goto v___jp_3393_;
}
}
}
v___jp_3467_:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_mkPrivateName(v___y_3475_, v___y_3477_);
lean_dec_ref(v___y_3475_);
v___y_3445_ = v___y_3468_;
v___y_3446_ = v___y_3469_;
v___y_3447_ = v___y_3471_;
v___y_3448_ = v___y_3479_;
v___y_3449_ = v___y_3472_;
v___y_3450_ = v___y_3478_;
v___y_3451_ = v___y_3473_;
v___y_3452_ = v___y_3480_;
v___y_3453_ = v___y_3485_;
v___y_3454_ = v___y_3484_;
v_declName_3455_ = v___x_3486_;
v___y_3456_ = v___y_3476_;
v___y_3457_ = v___y_3470_;
v___y_3458_ = v___y_3474_;
v___y_3459_ = v___y_3481_;
v___y_3460_ = v___y_3483_;
v___y_3461_ = v___y_3482_;
goto v___jp_3444_;
}
v___jp_3487_:
{
lean_object* v___x_3505_; lean_object* v_env_3506_; lean_object* v___x_3507_; uint8_t v_isModule_3508_; lean_object* v___x_3509_; 
v___x_3505_ = lean_st_ref_get(v___y_3500_);
v_env_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc_ref(v_env_3506_);
lean_dec(v___x_3505_);
v___x_3507_ = l_Lean_Environment_header(v_env_3506_);
v_isModule_3508_ = lean_ctor_get_uint8(v___x_3507_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3507_);
lean_inc(v___y_3502_);
v___x_3509_ = l_Lean_Name_append(v___y_3504_, v___y_3502_);
if (v_isModule_3508_ == 0)
{
lean_dec_ref(v_env_3506_);
v___y_3445_ = v___y_3488_;
v___y_3446_ = v___y_3489_;
v___y_3447_ = v___y_3491_;
v___y_3448_ = v___y_3496_;
v___y_3449_ = v___y_3492_;
v___y_3450_ = v___y_3497_;
v___y_3451_ = v___y_3493_;
v___y_3452_ = v___y_3499_;
v___y_3453_ = v___y_3502_;
v___y_3454_ = v___y_3503_;
v_declName_3455_ = v___x_3509_;
v___y_3456_ = v___y_3495_;
v___y_3457_ = v___y_3490_;
v___y_3458_ = v___y_3494_;
v___y_3459_ = v___y_3498_;
v___y_3460_ = v___y_3501_;
v___y_3461_ = v___y_3500_;
goto v___jp_3444_;
}
else
{
uint8_t v_isExporting_3510_; 
v_isExporting_3510_ = lean_ctor_get_uint8(v_env_3506_, sizeof(void*)*8);
if (v_isExporting_3510_ == 0)
{
v___y_3468_ = v___y_3488_;
v___y_3469_ = v___y_3489_;
v___y_3470_ = v___y_3490_;
v___y_3471_ = v___y_3491_;
v___y_3472_ = v___y_3492_;
v___y_3473_ = v___y_3493_;
v___y_3474_ = v___y_3494_;
v___y_3475_ = v_env_3506_;
v___y_3476_ = v___y_3495_;
v___y_3477_ = v___x_3509_;
v___y_3478_ = v___y_3497_;
v___y_3479_ = v___y_3496_;
v___y_3480_ = v___y_3499_;
v___y_3481_ = v___y_3498_;
v___y_3482_ = v___y_3500_;
v___y_3483_ = v___y_3501_;
v___y_3484_ = v___y_3503_;
v___y_3485_ = v___y_3502_;
goto v___jp_3467_;
}
else
{
if (v___y_3496_ == 0)
{
lean_dec_ref(v_env_3506_);
v___y_3445_ = v___y_3488_;
v___y_3446_ = v___y_3489_;
v___y_3447_ = v___y_3491_;
v___y_3448_ = v___y_3496_;
v___y_3449_ = v___y_3492_;
v___y_3450_ = v___y_3497_;
v___y_3451_ = v___y_3493_;
v___y_3452_ = v___y_3499_;
v___y_3453_ = v___y_3502_;
v___y_3454_ = v___y_3503_;
v_declName_3455_ = v___x_3509_;
v___y_3456_ = v___y_3495_;
v___y_3457_ = v___y_3490_;
v___y_3458_ = v___y_3494_;
v___y_3459_ = v___y_3498_;
v___y_3460_ = v___y_3501_;
v___y_3461_ = v___y_3500_;
goto v___jp_3444_;
}
else
{
v___y_3468_ = v___y_3488_;
v___y_3469_ = v___y_3489_;
v___y_3470_ = v___y_3490_;
v___y_3471_ = v___y_3491_;
v___y_3472_ = v___y_3492_;
v___y_3473_ = v___y_3493_;
v___y_3474_ = v___y_3494_;
v___y_3475_ = v_env_3506_;
v___y_3476_ = v___y_3495_;
v___y_3477_ = v___x_3509_;
v___y_3478_ = v___y_3497_;
v___y_3479_ = v___y_3496_;
v___y_3480_ = v___y_3499_;
v___y_3481_ = v___y_3498_;
v___y_3482_ = v___y_3500_;
v___y_3483_ = v___y_3501_;
v___y_3484_ = v___y_3503_;
v___y_3485_ = v___y_3502_;
goto v___jp_3467_;
}
}
}
}
v___jp_3511_:
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v___y_3520_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref(v___x_3526_);
v___x_3528_ = l_Lean_Syntax_getId(v___y_3517_);
if (lean_obj_tag(v_a_3527_) == 0)
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_box(0);
v___y_3488_ = v___y_3512_;
v___y_3489_ = v___y_3513_;
v___y_3490_ = v___y_3521_;
v___y_3491_ = v___y_3514_;
v___y_3492_ = v___y_3516_;
v___y_3493_ = v___y_3517_;
v___y_3494_ = v___y_3522_;
v___y_3495_ = v___y_3520_;
v___y_3496_ = v___y_3515_;
v___y_3497_ = v_a_3527_;
v___y_3498_ = v___y_3523_;
v___y_3499_ = v___y_3518_;
v___y_3500_ = v___y_3525_;
v___y_3501_ = v___y_3524_;
v___y_3502_ = v___x_3528_;
v___y_3503_ = v___y_3519_;
v___y_3504_ = v___x_3529_;
goto v___jp_3487_;
}
else
{
lean_object* v_val_3530_; 
v_val_3530_ = lean_ctor_get(v_a_3527_, 0);
lean_inc(v_val_3530_);
v___y_3488_ = v___y_3512_;
v___y_3489_ = v___y_3513_;
v___y_3490_ = v___y_3521_;
v___y_3491_ = v___y_3514_;
v___y_3492_ = v___y_3516_;
v___y_3493_ = v___y_3517_;
v___y_3494_ = v___y_3522_;
v___y_3495_ = v___y_3520_;
v___y_3496_ = v___y_3515_;
v___y_3497_ = v_a_3527_;
v___y_3498_ = v___y_3523_;
v___y_3499_ = v___y_3518_;
v___y_3500_ = v___y_3525_;
v___y_3501_ = v___y_3524_;
v___y_3502_ = v___x_3528_;
v___y_3503_ = v___y_3519_;
v___y_3504_ = v_val_3530_;
goto v___jp_3487_;
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v_b_3249_);
v_a_3531_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3526_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3526_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
v___jp_3539_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; 
v___x_3553_ = l_Lean_Syntax_getArg(v___y_3542_, v___x_3264_);
v___x_3554_ = l_Lean_Syntax_getArg(v___x_3553_, v___x_3264_);
lean_dec(v___x_3553_);
v___x_3555_ = l_Lean_Syntax_isIdent(v___x_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__1);
v___x_3557_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___x_3554_, v___x_3556_, v___y_3548_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3551_, v___y_3543_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_dec_ref(v___x_3557_);
v___y_3512_ = v___y_3540_;
v___y_3513_ = v___y_3541_;
v___y_3514_ = v___y_3542_;
v___y_3515_ = v___y_3549_;
v___y_3516_ = v___y_3544_;
v___y_3517_ = v___x_3554_;
v___y_3518_ = v___y_3550_;
v___y_3519_ = v___y_3552_;
v___y_3520_ = v___y_3548_;
v___y_3521_ = v___y_3545_;
v___y_3522_ = v___y_3546_;
v___y_3523_ = v___y_3547_;
v___y_3524_ = v___y_3551_;
v___y_3525_ = v___y_3543_;
goto v___jp_3511_;
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec(v___x_3554_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v_b_3249_);
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3557_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
else
{
v___y_3512_ = v___y_3540_;
v___y_3513_ = v___y_3541_;
v___y_3514_ = v___y_3542_;
v___y_3515_ = v___y_3549_;
v___y_3516_ = v___y_3544_;
v___y_3517_ = v___x_3554_;
v___y_3518_ = v___y_3550_;
v___y_3519_ = v___y_3552_;
v___y_3520_ = v___y_3548_;
v___y_3521_ = v___y_3545_;
v___y_3522_ = v___y_3546_;
v___y_3523_ = v___y_3547_;
v___y_3524_ = v___y_3551_;
v___y_3525_ = v___y_3543_;
goto v___jp_3511_;
}
}
v___jp_3566_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v___x_3575_ = lean_unsigned_to_nat(2u);
v___x_3576_ = l_Lean_Syntax_getArg(v_a_3266_, v___x_3575_);
v___x_3577_ = l_Lean_Syntax_getArg(v___x_3576_, v___x_3264_);
lean_dec(v___x_3576_);
v___x_3578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__3));
lean_inc(v___x_3577_);
v___x_3579_ = l_Lean_Syntax_isOfKind(v___x_3577_, v___x_3578_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__5));
lean_inc(v___x_3577_);
v___x_3581_ = l_Lean_Syntax_isOfKind(v___x_3577_, v___x_3580_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; uint8_t v___x_3583_; 
v___x_3582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__7));
lean_inc(v___x_3577_);
v___x_3583_ = l_Lean_Syntax_isOfKind(v___x_3577_, v___x_3582_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; 
lean_dec(v___x_3577_);
lean_dec_ref(v_attrs_3568_);
lean_dec(v___y_3567_);
v___x_3584_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__8___redArg();
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_dec_ref(v___x_3584_);
v_a_3258_ = v_b_3249_;
goto v___jp_3257_;
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec_ref(v_b_3249_);
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3584_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3584_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
else
{
v___y_3540_ = v___x_3579_;
v___y_3541_ = v___y_3567_;
v___y_3542_ = v___x_3577_;
v___y_3543_ = v___y_3574_;
v___y_3544_ = v_attrs_3568_;
v___y_3545_ = v___y_3570_;
v___y_3546_ = v___y_3571_;
v___y_3547_ = v___y_3572_;
v___y_3548_ = v___y_3569_;
v___y_3549_ = v___x_3579_;
v___y_3550_ = v___x_3575_;
v___y_3551_ = v___y_3573_;
v___y_3552_ = v___x_3581_;
goto v___jp_3539_;
}
}
else
{
v___y_3540_ = v___x_3579_;
v___y_3541_ = v___y_3567_;
v___y_3542_ = v___x_3577_;
v___y_3543_ = v___y_3574_;
v___y_3544_ = v_attrs_3568_;
v___y_3545_ = v___y_3570_;
v___y_3546_ = v___y_3571_;
v___y_3547_ = v___y_3572_;
v___y_3548_ = v___y_3569_;
v___y_3549_ = v___x_3579_;
v___y_3550_ = v___x_3575_;
v___y_3551_ = v___y_3573_;
v___y_3552_ = v___x_3581_;
goto v___jp_3539_;
}
}
else
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
lean_dec_ref(v_attrs_3568_);
lean_dec(v___y_3567_);
v___x_3593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___closed__9);
v___x_3594_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__7___redArg(v___x_3577_, v___x_3593_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___x_3577_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_dec_ref(v___x_3594_);
v_a_3258_ = v_b_3249_;
goto v___jp_3257_;
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
lean_dec_ref(v_b_3249_);
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
v___jp_3603_:
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = l_Lean_Syntax_getArg(v_a_3266_, v___x_3265_);
v___x_3606_ = l_Lean_Syntax_isNone(v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = l_Lean_Syntax_getArg(v___x_3605_, v___x_3264_);
lean_dec(v___x_3605_);
v___x_3608_ = l_Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9(v___x_3607_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___x_3607_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref(v___x_3608_);
v___y_3567_ = v___y_3604_;
v_attrs_3568_ = v_a_3609_;
v___y_3569_ = v___y_3250_;
v___y_3570_ = v___y_3251_;
v___y_3571_ = v___y_3252_;
v___y_3572_ = v___y_3253_;
v___y_3573_ = v___y_3254_;
v___y_3574_ = v___y_3255_;
goto v___jp_3566_;
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec(v___y_3604_);
lean_dec_ref(v_b_3249_);
v_a_3610_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3608_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3608_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v___x_3618_; 
lean_dec(v___x_3605_);
v___x_3618_ = ((lean_object*)(l_Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22___closed__0));
v___y_3567_ = v___y_3604_;
v_attrs_3568_ = v___x_3618_;
v___y_3569_ = v___y_3250_;
v___y_3570_ = v___y_3251_;
v___y_3571_ = v___y_3252_;
v___y_3572_ = v___y_3253_;
v___y_3573_ = v___y_3254_;
v___y_3574_ = v___y_3255_;
goto v___jp_3566_;
}
}
}
v___jp_3257_:
{
size_t v___x_3259_; size_t v___x_3260_; 
v___x_3259_ = ((size_t)1ULL);
v___x_3260_ = lean_usize_add(v_i_3248_, v___x_3259_);
v_i_3248_ = v___x_3260_;
v_b_3249_ = v_a_3258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10___boxed(lean_object* v___x_3632_, lean_object* v_as_3633_, lean_object* v_sz_3634_, lean_object* v_i_3635_, lean_object* v_b_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
uint8_t v___x_56405__boxed_3644_; size_t v_sz_boxed_3645_; size_t v_i_boxed_3646_; lean_object* v_res_3647_; 
v___x_56405__boxed_3644_ = lean_unbox(v___x_3632_);
v_sz_boxed_3645_ = lean_unbox_usize(v_sz_3634_);
lean_dec(v_sz_3634_);
v_i_boxed_3646_ = lean_unbox_usize(v_i_3635_);
lean_dec(v_i_3635_);
v_res_3647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(v___x_56405__boxed_3644_, v_as_3633_, v_sz_boxed_3645_, v_i_boxed_3646_, v_b_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v_as_3633_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(lean_object* v_letRec_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v_options_3658_; lean_object* v___x_3659_; lean_object* v_decls_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; size_t v_sz_3667_; size_t v___x_3668_; lean_object* v___x_3669_; 
v_options_3658_ = lean_ctor_get(v_a_3655_, 2);
v___x_3659_ = lean_unsigned_to_nat(0u);
v_decls_3660_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___closed__0));
v___x_3661_ = l_Lean_doc_verso;
v___x_3662_ = l_Lean_Option_get___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__0(v_options_3658_, v___x_3661_);
v___x_3663_ = lean_unsigned_to_nat(1u);
v___x_3664_ = l_Lean_Syntax_getArg(v_letRec_3650_, v___x_3663_);
v___x_3665_ = l_Lean_Syntax_getArg(v___x_3664_, v___x_3659_);
lean_dec(v___x_3664_);
v___x_3666_ = l_Lean_Syntax_getSepArgs(v___x_3665_);
lean_dec(v___x_3665_);
v_sz_3667_ = lean_array_size(v___x_3666_);
v___x_3668_ = ((size_t)0ULL);
v___x_3669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__10(v___x_3662_, v___x_3666_, v_sz_3667_, v___x_3668_, v_decls_3660_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_);
lean_dec_ref(v___x_3666_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3680_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3680_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3680_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3674_ = lean_unsigned_to_nat(3u);
v___x_3675_ = l_Lean_Syntax_getArg(v_letRec_3650_, v___x_3674_);
v___x_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3676_, 0, v_a_3670_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3676_);
v___x_3678_ = v___x_3672_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
v_a_3681_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3669_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3669_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView___boxed(lean_object* v_letRec_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
lean_object* v_res_3697_; 
v_res_3697_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(v_letRec_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_);
lean_dec(v_a_3695_);
lean_dec_ref(v_a_3694_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
lean_dec(v_letRec_3689_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5(lean_object* v_stx_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___redArg(v_stx_3698_, v___y_3703_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5___boxed(lean_object* v_stx_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__5(v_stx_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v_stx_3707_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6(lean_object* v_declName_3716_, lean_object* v_declRanges_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___redArg(v_declName_3716_, v_declRanges_3717_, v___y_3721_, v___y_3723_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6___boxed(lean_object* v_declName_3726_, lean_object* v_declRanges_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__2_spec__6(v_declName_3726_, v_declRanges_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
lean_dec_ref(v___y_3730_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(lean_object* v_00_u03b1_3736_, lean_object* v_x_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___redArg(v_x_3737_, v___y_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10___boxed(lean_object* v_00_u03b1_3741_, lean_object* v_x_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__10(v_00_u03b1_3741_, v_x_3742_, v___y_3743_, v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec_ref(v_x_3742_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(lean_object* v_00_u03b1_3746_, lean_object* v_ref_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___redArg(v_ref_3747_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14___boxed(lean_object* v_00_u03b1_3756_, lean_object* v_ref_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__14(v_00_u03b1_3756_, v_ref_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4(lean_object* v_00_u03b1_3766_, lean_object* v_x_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___redArg(v_x_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4___boxed(lean_object* v_00_u03b1_3776_, lean_object* v_x_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4(v_00_u03b1_3776_, v_x_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5(lean_object* v_00_u03b1_3786_, lean_object* v_msg_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v_msg_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___boxed(lean_object* v_00_u03b1_3796_, lean_object* v_msg_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5(v_00_u03b1_3796_, v_msg_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6(lean_object* v_t_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___redArg(v_t_3806_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6___boxed(lean_object* v_t_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__2_spec__6(v_t_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8(lean_object* v_env_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___redArg(v_env_3824_, v___y_3828_, v___y_3830_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8___boxed(lean_object* v_env_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
lean_object* v_res_3841_; 
v_res_3841_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3_spec__8(v_env_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3(lean_object* v_00_u03b1_3842_, lean_object* v_env_3843_, lean_object* v_x_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___redArg(v_env_3843_, v_x_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3___boxed(lean_object* v_00_u03b1_3853_, lean_object* v_env_3854_, lean_object* v_x_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_withEnv___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__3(v_00_u03b1_3853_, v_env_3854_, v_x_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(lean_object* v_cls_3864_, lean_object* v_msg_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___redArg(v_cls_3864_, v_msg_3865_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9___boxed(lean_object* v_cls_3874_, lean_object* v_msg_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__9(v_cls_3874_, v_msg_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(lean_object* v_as_3884_, lean_object* v_as_x27_3885_, lean_object* v_b_3886_, lean_object* v_a_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___redArg(v_as_x27_3885_, v_b_3886_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12___boxed(lean_object* v_as_3896_, lean_object* v_as_x27_3897_, lean_object* v_b_3898_, lean_object* v_a_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__12(v_as_3896_, v_as_x27_3897_, v_b_3898_, v_a_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v_as_x27_3897_);
lean_dec(v_as_3896_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(lean_object* v_msgData_3908_, lean_object* v_macroStack_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___redArg(v_msgData_3908_, v_macroStack_3909_, v___y_3914_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17___boxed(lean_object* v_msgData_3918_, lean_object* v_macroStack_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5_spec__17(v_msgData_3918_, v_macroStack_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19(lean_object* v_00_u03b2_3928_, lean_object* v_m_3929_, lean_object* v_a_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___redArg(v_m_3929_, v_a_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19___boxed(lean_object* v_00_u03b2_3932_, lean_object* v_m_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19(v_00_u03b2_3932_, v_m_3933_, v_a_3934_);
lean_dec(v_a_3934_);
lean_dec_ref(v_m_3933_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17(lean_object* v_00_u03b1_3936_, lean_object* v_constName_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___redArg(v_constName_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17___boxed(lean_object* v_00_u03b1_3946_, lean_object* v_constName_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17(v_00_u03b1_3946_, v_constName_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
return v_res_3955_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26(lean_object* v_00_u03b2_3956_, lean_object* v_x_3957_, lean_object* v_x_3958_){
_start:
{
uint8_t v___x_3959_; 
v___x_3959_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___redArg(v_x_3957_, v_x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26___boxed(lean_object* v_00_u03b2_3960_, lean_object* v_x_3961_, lean_object* v_x_3962_){
_start:
{
uint8_t v_res_3963_; lean_object* v_r_3964_; 
v_res_3963_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26(v_00_u03b2_3960_, v_x_3961_, v_x_3962_);
lean_dec_ref(v_x_3962_);
lean_dec_ref(v_x_3961_);
v_r_3964_ = lean_box(v_res_3963_);
return v_r_3964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29(lean_object* v_00_u03b2_3965_, lean_object* v_a_3966_, lean_object* v_x_3967_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___redArg(v_a_3966_, v_x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29___boxed(lean_object* v_00_u03b2_3969_, lean_object* v_a_3970_, lean_object* v_x_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__19_spec__29(v_00_u03b2_3969_, v_a_3970_, v_x_3971_);
lean_dec(v_x_3971_);
lean_dec(v_a_3970_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39(lean_object* v_00_u03b1_3973_, lean_object* v_x_3974_, uint8_t v_isExporting_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___redArg(v_x_3974_, v_isExporting_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39___boxed(lean_object* v_00_u03b1_3984_, lean_object* v_x_3985_, lean_object* v_isExporting_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
uint8_t v_isExporting_boxed_3994_; lean_object* v_res_3995_; 
v_isExporting_boxed_3994_ = lean_unbox(v_isExporting_3986_);
v_res_3995_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36_spec__39(v_00_u03b1_3984_, v_x_3985_, v_isExporting_boxed_3994_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36(lean_object* v_00_u03b1_3996_, lean_object* v_x_3997_, uint8_t v_when_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___redArg(v_x_3997_, v_when_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36___boxed(lean_object* v_00_u03b1_4007_, lean_object* v_x_4008_, lean_object* v_when_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
uint8_t v_when_boxed_4017_; lean_object* v_res_4018_; 
v_when_boxed_4017_ = lean_unbox(v_when_4009_);
v_res_4018_ = l_Lean_withoutExporting___at___00Lean_Elab_elabAttr___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__31_spec__36(v_00_u03b1_4007_, v_x_4008_, v_when_boxed_4017_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28(lean_object* v_00_u03b1_4019_, lean_object* v_ref_4020_, lean_object* v_constName_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___redArg(v_ref_4020_, v_constName_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28___boxed(lean_object* v_00_u03b1_4030_, lean_object* v_ref_4031_, lean_object* v_constName_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28(v_00_u03b1_4030_, v_ref_4031_, v_constName_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v_ref_4031_);
return v_res_4040_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32(lean_object* v_00_u03b2_4041_, lean_object* v_x_4042_, size_t v_x_4043_, lean_object* v_x_4044_){
_start:
{
uint8_t v___x_4045_; 
v___x_4045_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___redArg(v_x_4042_, v_x_4043_, v_x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32___boxed(lean_object* v_00_u03b2_4046_, lean_object* v_x_4047_, lean_object* v_x_4048_, lean_object* v_x_4049_){
_start:
{
size_t v_x_57599__boxed_4050_; uint8_t v_res_4051_; lean_object* v_r_4052_; 
v_x_57599__boxed_4050_ = lean_unbox_usize(v_x_4048_);
lean_dec(v_x_4048_);
v_res_4051_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32(v_00_u03b2_4046_, v_x_4047_, v_x_57599__boxed_4050_, v_x_4049_);
lean_dec_ref(v_x_4049_);
lean_dec_ref(v_x_4047_);
v_r_4052_ = lean_box(v_res_4051_);
return v_r_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42(lean_object* v_ref_4053_, lean_object* v_msgData_4054_, uint8_t v_severity_4055_, uint8_t v_isSilent_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v___x_4064_; 
v___x_4064_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___redArg(v_ref_4053_, v_msgData_4054_, v_severity_4055_, v_isSilent_4056_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42___boxed(lean_object* v_ref_4065_, lean_object* v_msgData_4066_, lean_object* v_severity_4067_, lean_object* v_isSilent_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
uint8_t v_severity_boxed_4076_; uint8_t v_isSilent_boxed_4077_; lean_object* v_res_4078_; 
v_severity_boxed_4076_ = lean_unbox(v_severity_4067_);
v_isSilent_boxed_4077_ = lean_unbox(v_isSilent_4068_);
v_res_4078_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_elabAttrs___at___00Lean_Elab_elabDeclAttrs___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__9_spec__22_spec__32_spec__38_spec__42(v_ref_4065_, v_msgData_4066_, v_severity_boxed_4076_, v_isSilent_boxed_4077_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v_ref_4065_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37(lean_object* v_00_u03b1_4079_, lean_object* v_ref_4080_, lean_object* v_msg_4081_, lean_object* v_declHint_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___redArg(v_ref_4080_, v_msg_4081_, v_declHint_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37___boxed(lean_object* v_00_u03b1_4091_, lean_object* v_ref_4092_, lean_object* v_msg_4093_, lean_object* v_declHint_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37(v_00_u03b1_4091_, v_ref_4092_, v_msg_4093_, v_declHint_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v_ref_4092_);
return v_res_4102_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40(lean_object* v_00_u03b2_4103_, lean_object* v_keys_4104_, lean_object* v_vals_4105_, lean_object* v_heq_4106_, lean_object* v_i_4107_, lean_object* v_k_4108_){
_start:
{
uint8_t v___x_4109_; 
v___x_4109_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___redArg(v_keys_4104_, v_i_4107_, v_k_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40___boxed(lean_object* v_00_u03b2_4110_, lean_object* v_keys_4111_, lean_object* v_vals_4112_, lean_object* v_heq_4113_, lean_object* v_i_4114_, lean_object* v_k_4115_){
_start:
{
uint8_t v_res_4116_; lean_object* v_r_4117_; 
v_res_4116_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__4_spec__11_spec__17_spec__26_spec__32_spec__40(v_00_u03b2_4110_, v_keys_4111_, v_vals_4112_, v_heq_4113_, v_i_4114_, v_k_4115_);
lean_dec_ref(v_k_4115_);
lean_dec_ref(v_vals_4112_);
lean_dec_ref(v_keys_4111_);
v_r_4117_ = lean_box(v_res_4116_);
return v_r_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48(lean_object* v_msg_4118_, lean_object* v_declHint_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___redArg(v_msg_4118_, v_declHint_4119_, v___y_4125_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48___boxed(lean_object* v_msg_4128_, lean_object* v_declHint_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1_spec__1_spec__3_spec__17_spec__28_spec__37_spec__44_spec__48(v_msg_4128_, v_declHint_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0(lean_object* v_k_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v_b_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v___x_4147_; 
lean_inc(v___y_4145_);
lean_inc_ref(v___y_4144_);
lean_inc(v___y_4143_);
lean_inc_ref(v___y_4142_);
lean_inc(v___y_4140_);
lean_inc_ref(v___y_4139_);
v___x_4147_ = lean_apply_8(v_k_4138_, v_b_4141_, v___y_4139_, v___y_4140_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, lean_box(0));
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v_b_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0(v_k_4148_, v___y_4149_, v___y_4150_, v_b_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(lean_object* v_shortDeclName_4158_, lean_object* v_type_4159_, lean_object* v_declName_4160_, lean_object* v_k_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___f_4169_; lean_object* v___x_4170_; 
lean_inc(v___y_4163_);
lean_inc_ref(v___y_4162_);
v___f_4169_ = lean_alloc_closure((void*)(l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_4169_, 0, v_k_4161_);
lean_closure_set(v___f_4169_, 1, v___y_4162_);
lean_closure_set(v___f_4169_, 2, v___y_4163_);
v___x_4170_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withAuxDeclImp(lean_box(0), v_shortDeclName_4158_, v_type_4159_, v_declName_4160_, v___f_4169_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_);
if (lean_obj_tag(v___x_4170_) == 0)
{
return v___x_4170_;
}
else
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4170_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4170_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4170_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg___boxed(lean_object* v_shortDeclName_4179_, lean_object* v_type_4180_, lean_object* v_declName_4181_, lean_object* v_k_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4179_, v_type_4180_, v_declName_4181_, v_k_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0(lean_object* v_00_u03b1_4191_, lean_object* v_shortDeclName_4192_, lean_object* v_type_4193_, lean_object* v_declName_4194_, lean_object* v_k_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4192_, v_type_4193_, v_declName_4194_, v_k_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___boxed(lean_object* v_00_u03b1_4204_, lean_object* v_shortDeclName_4205_, lean_object* v_type_4206_, lean_object* v_declName_4207_, lean_object* v_k_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0(v_00_u03b1_4204_, v_shortDeclName_4205_, v_type_4206_, v_declName_4207_, v_k_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0___boxed(lean_object* v_i_4217_, lean_object* v_fvars_4218_, lean_object* v_views_4219_, lean_object* v_k_4220_, lean_object* v_fvar_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0(v_i_4217_, v_fvars_4218_, v_views_4219_, v_k_4220_, v_fvar_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v_i_4217_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(lean_object* v_views_4230_, lean_object* v_k_4231_, lean_object* v_i_4232_, lean_object* v_fvars_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v___x_4241_; uint8_t v___x_4242_; 
v___x_4241_ = lean_array_get_size(v_views_4230_);
v___x_4242_ = lean_nat_dec_lt(v_i_4232_, v___x_4241_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; 
lean_dec(v_i_4232_);
lean_dec_ref(v_views_4230_);
lean_inc(v_a_4239_);
lean_inc_ref(v_a_4238_);
lean_inc(v_a_4237_);
lean_inc_ref(v_a_4236_);
lean_inc(v_a_4235_);
lean_inc_ref(v_a_4234_);
v___x_4243_ = lean_apply_8(v_k_4231_, v_fvars_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, lean_box(0));
return v___x_4243_;
}
else
{
lean_object* v_view_4244_; lean_object* v_shortDeclName_4245_; lean_object* v_declName_4246_; lean_object* v_type_4247_; lean_object* v___f_4248_; lean_object* v___x_4249_; 
v_view_4244_ = lean_array_fget_borrowed(v_views_4230_, v_i_4232_);
v_shortDeclName_4245_ = lean_ctor_get(v_view_4244_, 2);
lean_inc(v_shortDeclName_4245_);
v_declName_4246_ = lean_ctor_get(v_view_4244_, 3);
lean_inc(v_declName_4246_);
v_type_4247_ = lean_ctor_get(v_view_4244_, 7);
lean_inc_ref(v_type_4247_);
v___f_4248_ = lean_alloc_closure((void*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_4248_, 0, v_i_4232_);
lean_closure_set(v___f_4248_, 1, v_fvars_4233_);
lean_closure_set(v___f_4248_, 2, v_views_4230_);
lean_closure_set(v___f_4248_, 3, v_k_4231_);
v___x_4249_ = l_Lean_Meta_withAuxDecl___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop_spec__0___redArg(v_shortDeclName_4245_, v_type_4247_, v_declName_4246_, v___f_4248_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
return v___x_4249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___lam__0(lean_object* v_i_4250_, lean_object* v_fvars_4251_, lean_object* v_views_4252_, lean_object* v_k_4253_, lean_object* v_fvar_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4262_ = lean_unsigned_to_nat(1u);
v___x_4263_ = lean_nat_add(v_i_4250_, v___x_4262_);
v___x_4264_ = lean_array_push(v_fvars_4251_, v_fvar_4254_);
v___x_4265_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4252_, v_k_4253_, v___x_4263_, v___x_4264_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg___boxed(lean_object* v_views_4266_, lean_object* v_k_4267_, lean_object* v_i_4268_, lean_object* v_fvars_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4266_, v_k_4267_, v_i_4268_, v_fvars_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(lean_object* v_00_u03b1_4278_, lean_object* v_views_4279_, lean_object* v_k_4280_, lean_object* v_i_4281_, lean_object* v_fvars_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4279_, v_k_4280_, v_i_4281_, v_fvars_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___boxed(lean_object* v_00_u03b1_4291_, lean_object* v_views_4292_, lean_object* v_k_4293_, lean_object* v_i_4294_, lean_object* v_fvars_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop(v_00_u03b1_4291_, v_views_4292_, v_k_4293_, v_i_4294_, v_fvars_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(lean_object* v_views_4306_, lean_object* v_k_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4315_ = lean_unsigned_to_nat(0u);
v___x_4316_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___closed__0));
v___x_4317_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls_loop___redArg(v_views_4306_, v_k_4307_, v___x_4315_, v___x_4316_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg___boxed(lean_object* v_views_4318_, lean_object* v_k_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_views_4318_, v_k_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(lean_object* v_00_u03b1_4328_, lean_object* v_views_4329_, lean_object* v_k_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_views_4329_, v_k_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___boxed(lean_object* v_00_u03b1_4339_, lean_object* v_views_4340_, lean_object* v_k_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls(v_00_u03b1_4339_, v_views_4340_, v_k_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0(lean_object* v_k_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v_b_4353_, lean_object* v_c_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; 
lean_inc(v___y_4358_);
lean_inc_ref(v___y_4357_);
lean_inc(v___y_4356_);
lean_inc_ref(v___y_4355_);
lean_inc(v___y_4352_);
lean_inc_ref(v___y_4351_);
v___x_4360_ = lean_apply_9(v_k_4350_, v_b_4353_, v_c_4354_, v___y_4351_, v___y_4352_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, lean_box(0));
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0___boxed(lean_object* v_k_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v_b_4364_, lean_object* v_c_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0(v_k_4361_, v___y_4362_, v___y_4363_, v_b_4364_, v_c_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(lean_object* v_type_4372_, lean_object* v_maxFVars_x3f_4373_, lean_object* v_k_4374_, uint8_t v_cleanupAnnotations_4375_, uint8_t v_whnfType_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___f_4384_; lean_object* v___x_4385_; 
lean_inc(v___y_4378_);
lean_inc_ref(v___y_4377_);
v___f_4384_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4384_, 0, v_k_4374_);
lean_closure_set(v___f_4384_, 1, v___y_4377_);
lean_closure_set(v___f_4384_, 2, v___y_4378_);
v___x_4385_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4372_, v_maxFVars_x3f_4373_, v___f_4384_, v_cleanupAnnotations_4375_, v_whnfType_4376_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
if (lean_obj_tag(v___x_4385_) == 0)
{
return v___x_4385_;
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4385_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg___boxed(lean_object* v_type_4394_, lean_object* v_maxFVars_x3f_4395_, lean_object* v_k_4396_, lean_object* v_cleanupAnnotations_4397_, lean_object* v_whnfType_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4406_; uint8_t v_whnfType_boxed_4407_; lean_object* v_res_4408_; 
v_cleanupAnnotations_boxed_4406_ = lean_unbox(v_cleanupAnnotations_4397_);
v_whnfType_boxed_4407_ = lean_unbox(v_whnfType_4398_);
v_res_4408_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4394_, v_maxFVars_x3f_4395_, v_k_4396_, v_cleanupAnnotations_boxed_4406_, v_whnfType_boxed_4407_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1(lean_object* v_00_u03b1_4409_, lean_object* v_type_4410_, lean_object* v_maxFVars_x3f_4411_, lean_object* v_k_4412_, uint8_t v_cleanupAnnotations_4413_, uint8_t v_whnfType_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4410_, v_maxFVars_x3f_4411_, v_k_4412_, v_cleanupAnnotations_4413_, v_whnfType_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___boxed(lean_object* v_00_u03b1_4423_, lean_object* v_type_4424_, lean_object* v_maxFVars_x3f_4425_, lean_object* v_k_4426_, lean_object* v_cleanupAnnotations_4427_, lean_object* v_whnfType_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4436_; uint8_t v_whnfType_boxed_4437_; lean_object* v_res_4438_; 
v_cleanupAnnotations_boxed_4436_ = lean_unbox(v_cleanupAnnotations_4427_);
v_whnfType_boxed_4437_ = lean_unbox(v_whnfType_4428_);
v_res_4438_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1(v_00_u03b1_4423_, v_type_4424_, v_maxFVars_x3f_4425_, v_k_4426_, v_cleanupAnnotations_boxed_4436_, v_whnfType_boxed_4437_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0(lean_object* v_valStx_4439_, lean_object* v_x_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4448_, 0, v_x_4440_);
v___x_4449_ = l_Lean_Elab_Term_mkBodyInfo(v_valStx_4439_, v___x_4448_);
v___x_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4449_);
v___x_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0___boxed(lean_object* v_valStx_4452_, lean_object* v_x_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0(v_valStx_4452_, v_x_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(lean_object* v_upperBound_4462_, lean_object* v___x_4463_, lean_object* v_xs_4464_, lean_object* v_a_4465_, lean_object* v_b_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
uint8_t v___x_4474_; 
v___x_4474_ = lean_nat_dec_lt(v_a_4465_, v_upperBound_4462_);
if (v___x_4474_ == 0)
{
lean_object* v___x_4475_; 
lean_dec(v_a_4465_);
v___x_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4475_, 0, v_b_4466_);
return v___x_4475_;
}
else
{
lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___x_4476_ = l_Lean_instInhabitedExpr;
v___x_4477_ = lean_array_fget_borrowed(v___x_4463_, v_a_4465_);
v___x_4478_ = lean_array_get_borrowed(v___x_4476_, v_xs_4464_, v_a_4465_);
lean_inc(v___x_4478_);
lean_inc(v___x_4477_);
v___x_4479_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_4477_, v___x_4478_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
lean_dec_ref(v___x_4479_);
v___x_4480_ = lean_box(0);
v___x_4481_ = lean_unsigned_to_nat(1u);
v___x_4482_ = lean_nat_add(v_a_4465_, v___x_4481_);
lean_dec(v_a_4465_);
v_a_4465_ = v___x_4482_;
v_b_4466_ = v___x_4480_;
goto _start;
}
else
{
lean_dec(v_a_4465_);
return v___x_4479_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg___boxed(lean_object* v_upperBound_4484_, lean_object* v___x_4485_, lean_object* v_xs_4486_, lean_object* v_a_4487_, lean_object* v_b_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v_upperBound_4484_, v___x_4485_, v_xs_4486_, v_a_4487_, v_b_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec_ref(v_xs_4486_);
lean_dec_ref(v___x_4485_);
lean_dec(v_upperBound_4484_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1(lean_object* v_valStx_4497_, lean_object* v___x_4498_, uint8_t v___x_4499_, lean_object* v___x_4500_, lean_object* v_xs_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l_Lean_Elab_Term_elabTermEnsuringType(v_valStx_4497_, v___x_4498_, v___x_4499_, v___x_4499_, v___x_4500_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_object* v_a_4510_; uint8_t v___x_4511_; uint8_t v___x_4512_; lean_object* v___x_4513_; 
v_a_4510_ = lean_ctor_get(v___x_4509_, 0);
lean_inc(v_a_4510_);
lean_dec_ref(v___x_4509_);
v___x_4511_ = 0;
v___x_4512_ = 1;
v___x_4513_ = l_Lean_Meta_mkLambdaFVars(v_xs_4501_, v_a_4510_, v___x_4511_, v___x_4499_, v___x_4511_, v___x_4499_, v___x_4512_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
return v___x_4513_;
}
else
{
return v___x_4509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1___boxed(lean_object* v_valStx_4514_, lean_object* v___x_4515_, lean_object* v___x_4516_, lean_object* v___x_4517_, lean_object* v_xs_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
uint8_t v___x_3132__boxed_4526_; lean_object* v_res_4527_; 
v___x_3132__boxed_4526_ = lean_unbox(v___x_4516_);
v_res_4527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1(v_valStx_4514_, v___x_4515_, v___x_3132__boxed_4526_, v___x_4517_, v_xs_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec_ref(v_xs_4518_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2(lean_object* v___x_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v___x_4536_; 
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4528_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2___boxed(lean_object* v___x_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2(v___x_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
return v_res_4545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3(lean_object* v___x_4546_, lean_object* v_binderIds_4547_, lean_object* v_valStx_4548_, uint8_t v___x_4549_, lean_object* v___f_4550_, lean_object* v_declName_4551_, lean_object* v_xs_4552_, lean_object* v_type_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = lean_unsigned_to_nat(0u);
v___x_4562_ = lean_box(0);
v___x_4563_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v___x_4546_, v_binderIds_4547_, v_xs_4552_, v___x_4561_, v___x_4562_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___f_4567_; lean_object* v___x_4568_; lean_object* v___f_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
lean_dec_ref(v___x_4563_);
v___x_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4564_, 0, v_type_4553_);
v___x_4565_ = lean_box(0);
v___x_4566_ = lean_box(v___x_4549_);
lean_inc_n(v_valStx_4548_, 2);
v___f_4567_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4567_, 0, v_valStx_4548_);
lean_closure_set(v___f_4567_, 1, v___x_4564_);
lean_closure_set(v___f_4567_, 2, v___x_4566_);
lean_closure_set(v___f_4567_, 3, v___x_4565_);
lean_closure_set(v___f_4567_, 4, v_xs_4552_);
v___x_4568_ = l_Lean_Elab_Term_mkBodyInfo(v_valStx_4548_, v___x_4565_);
v___f_4569_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__2___boxed), 8, 1);
lean_closure_set(v___f_4569_, 0, v___x_4568_);
v___x_4570_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withInfoContext_x27___boxed), 11, 4);
lean_closure_set(v___x_4570_, 0, v_valStx_4548_);
lean_closure_set(v___x_4570_, 1, v___f_4567_);
lean_closure_set(v___x_4570_, 2, v___f_4550_);
lean_closure_set(v___x_4570_, 3, v___f_4569_);
v___x_4571_ = l_Lean_Elab_Term_withDeclName___redArg(v_declName_4551_, v___x_4570_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
return v___x_4571_;
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec_ref(v_type_4553_);
lean_dec_ref(v_xs_4552_);
lean_dec(v_declName_4551_);
lean_dec_ref(v___f_4550_);
lean_dec(v_valStx_4548_);
v_a_4572_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4563_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4563_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3___boxed(lean_object* v___x_4580_, lean_object* v_binderIds_4581_, lean_object* v_valStx_4582_, lean_object* v___x_4583_, lean_object* v___f_4584_, lean_object* v_declName_4585_, lean_object* v_xs_4586_, lean_object* v_type_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
uint8_t v___x_3199__boxed_4595_; lean_object* v_res_4596_; 
v___x_3199__boxed_4595_ = lean_unbox(v___x_4583_);
v_res_4596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3(v___x_4580_, v_binderIds_4581_, v_valStx_4582_, v___x_3199__boxed_4595_, v___f_4584_, v_declName_4585_, v_xs_4586_, v_type_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec_ref(v_binderIds_4581_);
lean_dec(v___x_4580_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(size_t v_sz_4597_, size_t v_i_4598_, lean_object* v_bs_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
uint8_t v___x_4607_; 
v___x_4607_ = lean_usize_dec_lt(v_i_4598_, v_sz_4597_);
if (v___x_4607_ == 0)
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4608_, 0, v_bs_4599_);
return v___x_4608_;
}
else
{
lean_object* v_v_4609_; lean_object* v_declName_4610_; lean_object* v_binderIds_4611_; lean_object* v_type_4612_; lean_object* v_valStx_4613_; lean_object* v___f_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___f_4617_; lean_object* v___x_4618_; uint8_t v___x_4619_; lean_object* v___x_4620_; 
v_v_4609_ = lean_array_uget_borrowed(v_bs_4599_, v_i_4598_);
v_declName_4610_ = lean_ctor_get(v_v_4609_, 3);
v_binderIds_4611_ = lean_ctor_get(v_v_4609_, 5);
v_type_4612_ = lean_ctor_get(v_v_4609_, 7);
v_valStx_4613_ = lean_ctor_get(v_v_4609_, 9);
lean_inc_n(v_valStx_4613_, 2);
v___f_4614_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4614_, 0, v_valStx_4613_);
v___x_4615_ = lean_array_get_size(v_binderIds_4611_);
v___x_4616_ = lean_box(v___x_4607_);
lean_inc(v_declName_4610_);
lean_inc_ref(v_binderIds_4611_);
v___f_4617_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___lam__3___boxed), 15, 6);
lean_closure_set(v___f_4617_, 0, v___x_4615_);
lean_closure_set(v___f_4617_, 1, v_binderIds_4611_);
lean_closure_set(v___f_4617_, 2, v_valStx_4613_);
lean_closure_set(v___f_4617_, 3, v___x_4616_);
lean_closure_set(v___f_4617_, 4, v___f_4614_);
lean_closure_set(v___f_4617_, 5, v_declName_4610_);
v___x_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___x_4615_);
v___x_4619_ = 0;
lean_inc_ref(v_type_4612_);
v___x_4620_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__1___redArg(v_type_4612_, v___x_4618_, v___f_4617_, v___x_4607_, v___x_4619_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
if (lean_obj_tag(v___x_4620_) == 0)
{
lean_object* v_a_4621_; lean_object* v___x_4622_; lean_object* v_bs_x27_4623_; size_t v___x_4624_; size_t v___x_4625_; lean_object* v___x_4626_; 
v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc(v_a_4621_);
lean_dec_ref(v___x_4620_);
v___x_4622_ = lean_unsigned_to_nat(0u);
v_bs_x27_4623_ = lean_array_uset(v_bs_4599_, v_i_4598_, v___x_4622_);
v___x_4624_ = ((size_t)1ULL);
v___x_4625_ = lean_usize_add(v_i_4598_, v___x_4624_);
v___x_4626_ = lean_array_uset(v_bs_x27_4623_, v_i_4598_, v_a_4621_);
v_i_4598_ = v___x_4625_;
v_bs_4599_ = v___x_4626_;
goto _start;
}
else
{
lean_object* v_a_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4635_; 
lean_dec_ref(v_bs_4599_);
v_a_4628_ = lean_ctor_get(v___x_4620_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4620_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4630_ = v___x_4620_;
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_a_4628_);
lean_dec(v___x_4620_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4635_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4633_; 
if (v_isShared_4631_ == 0)
{
v___x_4633_ = v___x_4630_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2___boxed(lean_object* v_sz_4636_, lean_object* v_i_4637_, lean_object* v_bs_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
size_t v_sz_boxed_4646_; size_t v_i_boxed_4647_; lean_object* v_res_4648_; 
v_sz_boxed_4646_ = lean_unbox_usize(v_sz_4636_);
lean_dec(v_sz_4636_);
v_i_boxed_4647_ = lean_unbox_usize(v_i_4637_);
lean_dec(v_i_4637_);
v_res_4648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(v_sz_boxed_4646_, v_i_boxed_4647_, v_bs_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(lean_object* v_view_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_){
_start:
{
lean_object* v_decls_4657_; size_t v_sz_4658_; size_t v___x_4659_; lean_object* v___x_4660_; 
v_decls_4657_ = lean_ctor_get(v_view_4649_, 0);
lean_inc_ref(v_decls_4657_);
lean_dec_ref(v_view_4649_);
v_sz_4658_ = lean_array_size(v_decls_4657_);
v___x_4659_ = ((size_t)0ULL);
v___x_4660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__2(v_sz_4658_, v___x_4659_, v_decls_4657_, v_a_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_);
return v___x_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues___boxed(lean_object* v_view_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(v_view_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_);
lean_dec(v_a_4667_);
lean_dec_ref(v_a_4666_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0(lean_object* v_upperBound_4670_, lean_object* v___x_4671_, lean_object* v_xs_4672_, lean_object* v_inst_4673_, lean_object* v_R_4674_, lean_object* v_a_4675_, lean_object* v_b_4676_, lean_object* v_c_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___redArg(v_upperBound_4670_, v___x_4671_, v_xs_4672_, v_a_4675_, v_b_4676_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0___boxed(lean_object* v_upperBound_4686_, lean_object* v___x_4687_, lean_object* v_xs_4688_, lean_object* v_inst_4689_, lean_object* v_R_4690_, lean_object* v_a_4691_, lean_object* v_b_4692_, lean_object* v_c_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues_spec__0(v_upperBound_4686_, v___x_4687_, v_xs_4688_, v_inst_4689_, v_R_4690_, v_a_4691_, v_b_4692_, v_c_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec_ref(v_xs_4688_);
lean_dec_ref(v___x_4687_);
lean_dec(v_upperBound_4686_);
return v_res_4701_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(lean_object* v_a_4702_, lean_object* v_x_4703_){
_start:
{
if (lean_obj_tag(v_x_4703_) == 0)
{
uint8_t v___x_4704_; 
v___x_4704_ = 0;
return v___x_4704_;
}
else
{
lean_object* v_head_4705_; lean_object* v_tail_4706_; lean_object* v_declName_4707_; lean_object* v_declName_4708_; uint8_t v___x_4709_; 
v_head_4705_ = lean_ctor_get(v_x_4703_, 0);
v_tail_4706_ = lean_ctor_get(v_x_4703_, 1);
v_declName_4707_ = lean_ctor_get(v_head_4705_, 4);
v_declName_4708_ = lean_ctor_get(v_a_4702_, 3);
v___x_4709_ = lean_name_eq(v_declName_4707_, v_declName_4708_);
if (v___x_4709_ == 0)
{
v_x_4703_ = v_tail_4706_;
goto _start;
}
else
{
return v___x_4709_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0___boxed(lean_object* v_a_4711_, lean_object* v_x_4712_){
_start:
{
uint8_t v_res_4713_; lean_object* v_r_4714_; 
v_res_4713_ = l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(v_a_4711_, v_x_4712_);
lean_dec(v_x_4712_);
lean_dec_ref(v_a_4711_);
v_r_4714_ = lean_box(v_res_4713_);
return v_r_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(lean_object* v___x_4715_, lean_object* v_as_4716_, size_t v_sz_4717_, size_t v_i_4718_, lean_object* v_b_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v_a_4728_; uint8_t v___x_4732_; 
v___x_4732_ = lean_usize_dec_lt(v_i_4718_, v_sz_4717_);
if (v___x_4732_ == 0)
{
lean_object* v___x_4733_; 
v___x_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4733_, 0, v_b_4719_);
return v___x_4733_;
}
else
{
lean_object* v___x_4734_; lean_object* v_a_4735_; uint8_t v___x_4736_; 
v___x_4734_ = lean_box(0);
v_a_4735_ = lean_array_uget_borrowed(v_as_4716_, v_i_4718_);
v___x_4736_ = l_List_any___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__0(v_a_4735_, v___x_4715_);
if (v___x_4736_ == 0)
{
v_a_4728_ = v___x_4734_;
goto v___jp_4727_;
}
else
{
lean_object* v_ref_4737_; lean_object* v_declName_4738_; lean_object* v_fileName_4739_; lean_object* v_fileMap_4740_; lean_object* v_options_4741_; lean_object* v_currRecDepth_4742_; lean_object* v_maxRecDepth_4743_; lean_object* v_ref_4744_; lean_object* v_currNamespace_4745_; lean_object* v_openDecls_4746_; lean_object* v_initHeartbeats_4747_; lean_object* v_maxHeartbeats_4748_; lean_object* v_quotContext_4749_; lean_object* v_currMacroScope_4750_; uint8_t v_diag_4751_; lean_object* v_cancelTk_x3f_4752_; uint8_t v_suppressElabErrors_4753_; lean_object* v_inheritedTraceOptions_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v_ref_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
v_ref_4737_ = lean_ctor_get(v_a_4735_, 0);
v_declName_4738_ = lean_ctor_get(v_a_4735_, 3);
v_fileName_4739_ = lean_ctor_get(v___y_4724_, 0);
v_fileMap_4740_ = lean_ctor_get(v___y_4724_, 1);
v_options_4741_ = lean_ctor_get(v___y_4724_, 2);
v_currRecDepth_4742_ = lean_ctor_get(v___y_4724_, 3);
v_maxRecDepth_4743_ = lean_ctor_get(v___y_4724_, 4);
v_ref_4744_ = lean_ctor_get(v___y_4724_, 5);
v_currNamespace_4745_ = lean_ctor_get(v___y_4724_, 6);
v_openDecls_4746_ = lean_ctor_get(v___y_4724_, 7);
v_initHeartbeats_4747_ = lean_ctor_get(v___y_4724_, 8);
v_maxHeartbeats_4748_ = lean_ctor_get(v___y_4724_, 9);
v_quotContext_4749_ = lean_ctor_get(v___y_4724_, 10);
v_currMacroScope_4750_ = lean_ctor_get(v___y_4724_, 11);
v_diag_4751_ = lean_ctor_get_uint8(v___y_4724_, sizeof(void*)*14);
v_cancelTk_x3f_4752_ = lean_ctor_get(v___y_4724_, 12);
v_suppressElabErrors_4753_ = lean_ctor_get_uint8(v___y_4724_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4754_ = lean_ctor_get(v___y_4724_, 13);
v___x_4755_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__1);
lean_inc(v_declName_4738_);
v___x_4756_ = l_Lean_MessageData_ofName(v_declName_4738_);
v___x_4757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4755_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
v___x_4758_ = lean_obj_once(&l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3, &l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3_once, _init_l_Lean_Elab_checkNotAlreadyDeclared___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__1___lam__5___closed__3);
v___x_4759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4757_);
lean_ctor_set(v___x_4759_, 1, v___x_4758_);
v_ref_4760_ = l_Lean_replaceRef(v_ref_4737_, v_ref_4744_);
lean_inc_ref(v_inheritedTraceOptions_4754_);
lean_inc(v_cancelTk_x3f_4752_);
lean_inc(v_currMacroScope_4750_);
lean_inc(v_quotContext_4749_);
lean_inc(v_maxHeartbeats_4748_);
lean_inc(v_initHeartbeats_4747_);
lean_inc(v_openDecls_4746_);
lean_inc(v_currNamespace_4745_);
lean_inc(v_maxRecDepth_4743_);
lean_inc(v_currRecDepth_4742_);
lean_inc_ref(v_options_4741_);
lean_inc_ref(v_fileMap_4740_);
lean_inc_ref(v_fileName_4739_);
v___x_4761_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4761_, 0, v_fileName_4739_);
lean_ctor_set(v___x_4761_, 1, v_fileMap_4740_);
lean_ctor_set(v___x_4761_, 2, v_options_4741_);
lean_ctor_set(v___x_4761_, 3, v_currRecDepth_4742_);
lean_ctor_set(v___x_4761_, 4, v_maxRecDepth_4743_);
lean_ctor_set(v___x_4761_, 5, v_ref_4760_);
lean_ctor_set(v___x_4761_, 6, v_currNamespace_4745_);
lean_ctor_set(v___x_4761_, 7, v_openDecls_4746_);
lean_ctor_set(v___x_4761_, 8, v_initHeartbeats_4747_);
lean_ctor_set(v___x_4761_, 9, v_maxHeartbeats_4748_);
lean_ctor_set(v___x_4761_, 10, v_quotContext_4749_);
lean_ctor_set(v___x_4761_, 11, v_currMacroScope_4750_);
lean_ctor_set(v___x_4761_, 12, v_cancelTk_x3f_4752_);
lean_ctor_set(v___x_4761_, 13, v_inheritedTraceOptions_4754_);
lean_ctor_set_uint8(v___x_4761_, sizeof(void*)*14, v_diag_4751_);
lean_ctor_set_uint8(v___x_4761_, sizeof(void*)*14 + 1, v_suppressElabErrors_4753_);
v___x_4762_ = l_Lean_throwError___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView_spec__5___redArg(v___x_4759_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___x_4761_, v___y_4725_);
lean_dec_ref(v___x_4761_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_dec_ref(v___x_4762_);
v_a_4728_ = v___x_4734_;
goto v___jp_4727_;
}
else
{
return v___x_4762_;
}
}
}
v___jp_4727_:
{
size_t v___x_4729_; size_t v___x_4730_; 
v___x_4729_ = ((size_t)1ULL);
v___x_4730_ = lean_usize_add(v_i_4718_, v___x_4729_);
v_i_4718_ = v___x_4730_;
v_b_4719_ = v_a_4728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1___boxed(lean_object* v___x_4763_, lean_object* v_as_4764_, lean_object* v_sz_4765_, lean_object* v_i_4766_, lean_object* v_b_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
size_t v_sz_boxed_4775_; size_t v_i_boxed_4776_; lean_object* v_res_4777_; 
v_sz_boxed_4775_ = lean_unbox_usize(v_sz_4765_);
lean_dec(v_sz_4765_);
v_i_boxed_4776_ = lean_unbox_usize(v_i_4766_);
lean_dec(v_i_4766_);
v_res_4777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(v___x_4763_, v_as_4764_, v_sz_boxed_4775_, v_i_boxed_4776_, v_b_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
lean_dec_ref(v_as_4764_);
lean_dec(v___x_4763_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(lean_object* v_values_4778_, lean_object* v_fvars_4779_, lean_object* v___x_4780_, lean_object* v___x_4781_, lean_object* v_as_4782_, lean_object* v_i_4783_, lean_object* v_j_4784_, lean_object* v_bs_4785_){
_start:
{
lean_object* v_zero_4787_; uint8_t v_isZero_4788_; 
v_zero_4787_ = lean_unsigned_to_nat(0u);
v_isZero_4788_ = lean_nat_dec_eq(v_i_4783_, v_zero_4787_);
if (v_isZero_4788_ == 1)
{
lean_object* v___x_4789_; 
lean_dec(v_j_4784_);
lean_dec(v_i_4783_);
lean_dec_ref(v___x_4781_);
lean_dec_ref(v___x_4780_);
v___x_4789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4789_, 0, v_bs_4785_);
return v___x_4789_;
}
else
{
lean_object* v___x_4790_; lean_object* v_ref_4791_; lean_object* v_attrs_4792_; lean_object* v_shortDeclName_4793_; lean_object* v_declName_4794_; lean_object* v_parentName_x3f_4795_; lean_object* v_binderIds_4796_; lean_object* v_binders_4797_; lean_object* v_type_4798_; lean_object* v_mvar_4799_; lean_object* v_termination_4800_; lean_object* v_docString_x3f_4801_; lean_object* v___x_4802_; lean_object* v_one_4803_; lean_object* v_n_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4790_ = lean_array_fget_borrowed(v_as_4782_, v_j_4784_);
v_ref_4791_ = lean_ctor_get(v___x_4790_, 0);
v_attrs_4792_ = lean_ctor_get(v___x_4790_, 1);
v_shortDeclName_4793_ = lean_ctor_get(v___x_4790_, 2);
v_declName_4794_ = lean_ctor_get(v___x_4790_, 3);
v_parentName_x3f_4795_ = lean_ctor_get(v___x_4790_, 4);
v_binderIds_4796_ = lean_ctor_get(v___x_4790_, 5);
v_binders_4797_ = lean_ctor_get(v___x_4790_, 6);
v_type_4798_ = lean_ctor_get(v___x_4790_, 7);
v_mvar_4799_ = lean_ctor_get(v___x_4790_, 8);
v_termination_4800_ = lean_ctor_get(v___x_4790_, 10);
v_docString_x3f_4801_ = lean_ctor_get(v___x_4790_, 11);
v___x_4802_ = l_Lean_instInhabitedExpr;
v_one_4803_ = lean_unsigned_to_nat(1u);
v_n_4804_ = lean_nat_sub(v_i_4783_, v_one_4803_);
lean_dec(v_i_4783_);
v___x_4805_ = lean_array_get_borrowed(v___x_4802_, v_values_4778_, v_j_4784_);
v___x_4806_ = lean_array_get_size(v_binderIds_4796_);
lean_inc_ref(v_termination_4800_);
v___x_4807_ = l_Lean_Elab_TerminationHints_rememberExtraParams(v___x_4806_, v_termination_4800_, v___x_4805_);
v___x_4808_ = lean_array_get_borrowed(v___x_4802_, v_fvars_4779_, v_j_4784_);
v___x_4809_ = l_Lean_Expr_fvarId_x21(v___x_4808_);
v___x_4810_ = l_Lean_Expr_mvarId_x21(v_mvar_4799_);
lean_inc(v_docString_x3f_4801_);
lean_inc(v_binders_4797_);
lean_inc(v___x_4805_);
lean_inc_ref(v_type_4798_);
lean_inc_ref(v___x_4781_);
lean_inc_ref(v___x_4780_);
lean_inc(v_parentName_x3f_4795_);
lean_inc(v_declName_4794_);
lean_inc(v_shortDeclName_4793_);
lean_inc_ref(v_attrs_4792_);
lean_inc(v_ref_4791_);
v___x_4811_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v___x_4811_, 0, v_ref_4791_);
lean_ctor_set(v___x_4811_, 1, v___x_4809_);
lean_ctor_set(v___x_4811_, 2, v_attrs_4792_);
lean_ctor_set(v___x_4811_, 3, v_shortDeclName_4793_);
lean_ctor_set(v___x_4811_, 4, v_declName_4794_);
lean_ctor_set(v___x_4811_, 5, v_parentName_x3f_4795_);
lean_ctor_set(v___x_4811_, 6, v___x_4780_);
lean_ctor_set(v___x_4811_, 7, v___x_4781_);
lean_ctor_set(v___x_4811_, 8, v_type_4798_);
lean_ctor_set(v___x_4811_, 9, v___x_4805_);
lean_ctor_set(v___x_4811_, 10, v___x_4810_);
lean_ctor_set(v___x_4811_, 11, v___x_4807_);
lean_ctor_set(v___x_4811_, 12, v_binders_4797_);
lean_ctor_set(v___x_4811_, 13, v_docString_x3f_4801_);
v___x_4812_ = lean_nat_add(v_j_4784_, v_one_4803_);
lean_dec(v_j_4784_);
v___x_4813_ = lean_array_push(v_bs_4785_, v___x_4811_);
v_i_4783_ = v_n_4804_;
v_j_4784_ = v___x_4812_;
v_bs_4785_ = v___x_4813_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg___boxed(lean_object* v_values_4815_, lean_object* v_fvars_4816_, lean_object* v___x_4817_, lean_object* v___x_4818_, lean_object* v_as_4819_, lean_object* v_i_4820_, lean_object* v_j_4821_, lean_object* v_bs_4822_, lean_object* v___y_4823_){
_start:
{
lean_object* v_res_4824_; 
v_res_4824_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(v_values_4815_, v_fvars_4816_, v___x_4817_, v___x_4818_, v_as_4819_, v_i_4820_, v_j_4821_, v_bs_4822_);
lean_dec_ref(v_as_4819_);
lean_dec_ref(v_fvars_4816_);
lean_dec_ref(v_values_4815_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(lean_object* v_views_4825_, lean_object* v_fvars_4826_, lean_object* v_values_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_){
_start:
{
lean_object* v___x_4835_; lean_object* v_letRecsToLift_4836_; lean_object* v___x_4837_; size_t v_sz_4838_; size_t v___x_4839_; lean_object* v___x_4840_; 
v___x_4835_ = lean_st_ref_get(v_a_4829_);
v_letRecsToLift_4836_ = lean_ctor_get(v___x_4835_, 6);
lean_inc(v_letRecsToLift_4836_);
lean_dec(v___x_4835_);
v___x_4837_ = lean_box(0);
v_sz_4838_ = lean_array_size(v_views_4825_);
v___x_4839_ = ((size_t)0ULL);
v___x_4840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__1(v_letRecsToLift_4836_, v_views_4825_, v_sz_4838_, v___x_4839_, v___x_4837_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_);
lean_dec(v_letRecsToLift_4836_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_lctx_4841_; lean_object* v_localInstances_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4872_; 
lean_dec_ref(v___x_4840_);
v_lctx_4841_ = lean_ctor_get(v_a_4830_, 2);
v_localInstances_4842_ = lean_ctor_get(v_a_4830_, 3);
v___x_4843_ = lean_array_get_size(v_views_4825_);
v___x_4844_ = lean_unsigned_to_nat(0u);
v___x_4845_ = lean_mk_empty_array_with_capacity(v___x_4843_);
lean_inc_ref(v_localInstances_4842_);
lean_inc_ref(v_lctx_4841_);
v___x_4846_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(v_values_4827_, v_fvars_4826_, v_lctx_4841_, v_localInstances_4842_, v_views_4825_, v___x_4843_, v___x_4844_, v___x_4845_);
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4849_ = v___x_4846_;
v_isShared_4850_ = v_isSharedCheck_4872_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4846_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4872_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4851_; lean_object* v_levelNames_4852_; lean_object* v_syntheticMVars_4853_; lean_object* v_pendingMVars_4854_; lean_object* v_mvarErrorInfos_4855_; lean_object* v_levelMVarErrorInfos_4856_; lean_object* v_mvarArgNames_4857_; lean_object* v_letRecsToLift_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4871_; 
v___x_4851_ = lean_st_ref_take(v_a_4829_);
v_levelNames_4852_ = lean_ctor_get(v___x_4851_, 0);
v_syntheticMVars_4853_ = lean_ctor_get(v___x_4851_, 1);
v_pendingMVars_4854_ = lean_ctor_get(v___x_4851_, 2);
v_mvarErrorInfos_4855_ = lean_ctor_get(v___x_4851_, 3);
v_levelMVarErrorInfos_4856_ = lean_ctor_get(v___x_4851_, 4);
v_mvarArgNames_4857_ = lean_ctor_get(v___x_4851_, 5);
v_letRecsToLift_4858_ = lean_ctor_get(v___x_4851_, 6);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4860_ = v___x_4851_;
v_isShared_4861_ = v_isSharedCheck_4871_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_letRecsToLift_4858_);
lean_inc(v_mvarArgNames_4857_);
lean_inc(v_levelMVarErrorInfos_4856_);
lean_inc(v_mvarErrorInfos_4855_);
lean_inc(v_pendingMVars_4854_);
lean_inc(v_syntheticMVars_4853_);
lean_inc(v_levelNames_4852_);
lean_dec(v___x_4851_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4871_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4862_ = lean_array_to_list(v_a_4847_);
v___x_4863_ = l_List_appendTR___redArg(v___x_4862_, v_letRecsToLift_4858_);
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 6, v___x_4863_);
v___x_4865_ = v___x_4860_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_levelNames_4852_);
lean_ctor_set(v_reuseFailAlloc_4870_, 1, v_syntheticMVars_4853_);
lean_ctor_set(v_reuseFailAlloc_4870_, 2, v_pendingMVars_4854_);
lean_ctor_set(v_reuseFailAlloc_4870_, 3, v_mvarErrorInfos_4855_);
lean_ctor_set(v_reuseFailAlloc_4870_, 4, v_levelMVarErrorInfos_4856_);
lean_ctor_set(v_reuseFailAlloc_4870_, 5, v_mvarArgNames_4857_);
lean_ctor_set(v_reuseFailAlloc_4870_, 6, v___x_4863_);
v___x_4865_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
lean_object* v___x_4866_; lean_object* v___x_4868_; 
v___x_4866_ = lean_st_ref_set(v_a_4829_, v___x_4865_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v___x_4837_);
v___x_4868_ = v___x_4849_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4837_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
}
else
{
return v___x_4840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift___boxed(lean_object* v_views_4873_, lean_object* v_fvars_4874_, lean_object* v_values_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_){
_start:
{
lean_object* v_res_4883_; 
v_res_4883_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(v_views_4873_, v_fvars_4874_, v_values_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_);
lean_dec(v_a_4881_);
lean_dec_ref(v_a_4880_);
lean_dec(v_a_4879_);
lean_dec_ref(v_a_4878_);
lean_dec(v_a_4877_);
lean_dec_ref(v_a_4876_);
lean_dec_ref(v_values_4875_);
lean_dec_ref(v_fvars_4874_);
lean_dec_ref(v_views_4873_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2(lean_object* v_values_4884_, lean_object* v_fvars_4885_, lean_object* v___x_4886_, lean_object* v___x_4887_, lean_object* v_as_4888_, lean_object* v_i_4889_, lean_object* v_j_4890_, lean_object* v_inv_4891_, lean_object* v_bs_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v___x_4900_; 
v___x_4900_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___redArg(v_values_4884_, v_fvars_4885_, v___x_4886_, v___x_4887_, v_as_4888_, v_i_4889_, v_j_4890_, v_bs_4892_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2___boxed(lean_object* v_values_4901_, lean_object* v_fvars_4902_, lean_object* v___x_4903_, lean_object* v___x_4904_, lean_object* v_as_4905_, lean_object* v_i_4906_, lean_object* v_j_4907_, lean_object* v_inv_4908_, lean_object* v_bs_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v_res_4917_; 
v_res_4917_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift_spec__2(v_values_4901_, v_fvars_4902_, v___x_4903_, v___x_4904_, v_as_4905_, v_i_4906_, v_j_4907_, v_inv_4908_, v_bs_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
lean_dec(v___y_4915_);
lean_dec_ref(v___y_4914_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
lean_dec_ref(v_as_4905_);
lean_dec_ref(v_fvars_4902_);
lean_dec_ref(v_values_4901_);
return v_res_4917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(size_t v_sz_4918_, size_t v_i_4919_, lean_object* v_bs_4920_){
_start:
{
uint8_t v___x_4921_; 
v___x_4921_ = lean_usize_dec_lt(v_i_4919_, v_sz_4918_);
if (v___x_4921_ == 0)
{
return v_bs_4920_;
}
else
{
lean_object* v_v_4922_; lean_object* v_mvar_4923_; lean_object* v___x_4924_; lean_object* v_bs_x27_4925_; size_t v___x_4926_; size_t v___x_4927_; lean_object* v___x_4928_; 
v_v_4922_ = lean_array_uget_borrowed(v_bs_4920_, v_i_4919_);
v_mvar_4923_ = lean_ctor_get(v_v_4922_, 8);
lean_inc_ref(v_mvar_4923_);
v___x_4924_ = lean_unsigned_to_nat(0u);
v_bs_x27_4925_ = lean_array_uset(v_bs_4920_, v_i_4919_, v___x_4924_);
v___x_4926_ = ((size_t)1ULL);
v___x_4927_ = lean_usize_add(v_i_4919_, v___x_4926_);
v___x_4928_ = lean_array_uset(v_bs_x27_4925_, v_i_4919_, v_mvar_4923_);
v_i_4919_ = v___x_4927_;
v_bs_4920_ = v___x_4928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1___boxed(lean_object* v_sz_4930_, lean_object* v_i_4931_, lean_object* v_bs_4932_){
_start:
{
size_t v_sz_boxed_4933_; size_t v_i_boxed_4934_; lean_object* v_res_4935_; 
v_sz_boxed_4933_ = lean_unbox_usize(v_sz_4930_);
lean_dec(v_sz_4930_);
v_i_boxed_4934_ = lean_unbox_usize(v_i_4931_);
lean_dec(v_i_4931_);
v_res_4935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(v_sz_boxed_4933_, v_i_boxed_4934_, v_bs_4932_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(lean_object* v_as_4936_, size_t v_sz_4937_, size_t v_i_4938_, lean_object* v_b_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
uint8_t v___x_4947_; 
v___x_4947_ = lean_usize_dec_lt(v_i_4938_, v_sz_4937_);
if (v___x_4947_ == 0)
{
lean_object* v___x_4948_; 
v___x_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4948_, 0, v_b_4939_);
return v___x_4948_;
}
else
{
lean_object* v_array_4949_; lean_object* v_start_4950_; lean_object* v_stop_4951_; uint8_t v___x_4952_; 
v_array_4949_ = lean_ctor_get(v_b_4939_, 0);
v_start_4950_ = lean_ctor_get(v_b_4939_, 1);
v_stop_4951_ = lean_ctor_get(v_b_4939_, 2);
v___x_4952_ = lean_nat_dec_lt(v_start_4950_, v_stop_4951_);
if (v___x_4952_ == 0)
{
lean_object* v___x_4953_; 
v___x_4953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4953_, 0, v_b_4939_);
return v___x_4953_;
}
else
{
lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4977_; 
lean_inc(v_stop_4951_);
lean_inc(v_start_4950_);
lean_inc_ref(v_array_4949_);
v_isSharedCheck_4977_ = !lean_is_exclusive(v_b_4939_);
if (v_isSharedCheck_4977_ == 0)
{
lean_object* v_unused_4978_; lean_object* v_unused_4979_; lean_object* v_unused_4980_; 
v_unused_4978_ = lean_ctor_get(v_b_4939_, 2);
lean_dec(v_unused_4978_);
v_unused_4979_ = lean_ctor_get(v_b_4939_, 1);
lean_dec(v_unused_4979_);
v_unused_4980_ = lean_ctor_get(v_b_4939_, 0);
lean_dec(v_unused_4980_);
v___x_4955_ = v_b_4939_;
v_isShared_4956_ = v_isSharedCheck_4977_;
goto v_resetjp_4954_;
}
else
{
lean_dec(v_b_4939_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4977_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v_a_4957_; lean_object* v_ref_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
v_a_4957_ = lean_array_uget_borrowed(v_as_4936_, v_i_4938_);
v_ref_4958_ = lean_ctor_get(v_a_4957_, 0);
v___x_4959_ = lean_array_fget_borrowed(v_array_4949_, v_start_4950_);
lean_inc(v___x_4959_);
lean_inc(v_ref_4958_);
v___x_4960_ = l_Lean_Elab_Term_addLocalVarInfo(v_ref_4958_, v___x_4959_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4964_; 
lean_dec_ref(v___x_4960_);
v___x_4961_ = lean_unsigned_to_nat(1u);
v___x_4962_ = lean_nat_add(v_start_4950_, v___x_4961_);
lean_dec(v_start_4950_);
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 1, v___x_4962_);
v___x_4964_ = v___x_4955_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_array_4949_);
lean_ctor_set(v_reuseFailAlloc_4968_, 1, v___x_4962_);
lean_ctor_set(v_reuseFailAlloc_4968_, 2, v_stop_4951_);
v___x_4964_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
size_t v___x_4965_; size_t v___x_4966_; 
v___x_4965_ = ((size_t)1ULL);
v___x_4966_ = lean_usize_add(v_i_4938_, v___x_4965_);
v_i_4938_ = v___x_4966_;
v_b_4939_ = v___x_4964_;
goto _start;
}
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_del_object(v___x_4955_);
lean_dec(v_stop_4951_);
lean_dec(v_start_4950_);
lean_dec_ref(v_array_4949_);
v_a_4969_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4960_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4960_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0___boxed(lean_object* v_as_4981_, lean_object* v_sz_4982_, lean_object* v_i_4983_, lean_object* v_b_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
size_t v_sz_boxed_4992_; size_t v_i_boxed_4993_; lean_object* v_res_4994_; 
v_sz_boxed_4992_ = lean_unbox_usize(v_sz_4982_);
lean_dec(v_sz_4982_);
v_i_boxed_4993_ = lean_unbox_usize(v_i_4983_);
lean_dec(v_i_4983_);
v_res_4994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(v_as_4981_, v_sz_boxed_4992_, v_i_boxed_4993_, v_b_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
lean_dec(v___y_4986_);
lean_dec_ref(v___y_4985_);
lean_dec_ref(v_as_4981_);
return v_res_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0(lean_object* v_decls_4995_, lean_object* v_a_4996_, lean_object* v_body_4997_, lean_object* v_expectedType_x3f_4998_, lean_object* v_fvars_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; size_t v_sz_5010_; size_t v___x_5011_; lean_object* v___x_5012_; 
v___x_5007_ = lean_unsigned_to_nat(0u);
v___x_5008_ = lean_array_get_size(v_fvars_4999_);
lean_inc_ref(v_fvars_4999_);
v___x_5009_ = l_Array_toSubarray___redArg(v_fvars_4999_, v___x_5007_, v___x_5008_);
v_sz_5010_ = lean_array_size(v_decls_4995_);
v___x_5011_ = ((size_t)0ULL);
v___x_5012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_elabLetRec_spec__0(v_decls_4995_, v_sz_5010_, v___x_5011_, v___x_5009_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v___x_5013_; 
lean_dec_ref(v___x_5012_);
v___x_5013_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRecDeclValues(v_a_4996_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_object* v_a_5014_; uint8_t v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v_a_5014_ = lean_ctor_get(v___x_5013_, 0);
lean_inc(v_a_5014_);
lean_dec_ref(v___x_5013_);
v___x_5015_ = 1;
v___x_5016_ = lean_box(0);
v___x_5017_ = l_Lean_Elab_Term_elabTermEnsuringType(v_body_4997_, v_expectedType_x3f_4998_, v___x_5015_, v___x_5015_, v___x_5016_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5019_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
lean_inc(v_a_5018_);
lean_dec_ref(v___x_5017_);
v___x_5019_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_registerLetRecsToLift(v_decls_4995_, v_fvars_4999_, v_a_5014_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
lean_dec(v_a_5014_);
if (lean_obj_tag(v___x_5019_) == 0)
{
uint8_t v___x_5020_; uint8_t v___x_5021_; lean_object* v___x_5022_; 
lean_dec_ref(v___x_5019_);
v___x_5020_ = 0;
v___x_5021_ = 1;
v___x_5022_ = l_Lean_Meta_mkLambdaFVars(v_fvars_4999_, v_a_5018_, v___x_5020_, v___x_5015_, v___x_5020_, v___x_5015_, v___x_5021_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
lean_dec_ref(v_fvars_4999_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5032_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5022_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5025_ = v___x_5022_;
v_isShared_5026_ = v_isSharedCheck_5032_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v___x_5022_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5032_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5030_; 
v___x_5027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_elabLetRec_spec__1(v_sz_5010_, v___x_5011_, v_decls_4995_);
v___x_5028_ = l_Lean_mkAppN(v_a_5023_, v___x_5027_);
lean_dec_ref(v___x_5027_);
if (v_isShared_5026_ == 0)
{
lean_ctor_set(v___x_5025_, 0, v___x_5028_);
v___x_5030_ = v___x_5025_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v___x_5028_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
else
{
lean_dec_ref(v_decls_4995_);
return v___x_5022_;
}
}
else
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5040_; 
lean_dec(v_a_5018_);
lean_dec_ref(v_fvars_4999_);
lean_dec_ref(v_decls_4995_);
v_a_5033_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_5035_ = v___x_5019_;
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v___x_5019_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5040_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5038_; 
if (v_isShared_5036_ == 0)
{
v___x_5038_ = v___x_5035_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5033_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
else
{
lean_dec(v_a_5014_);
lean_dec_ref(v_fvars_4999_);
lean_dec_ref(v_decls_4995_);
return v___x_5017_;
}
}
else
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5048_; 
lean_dec_ref(v_fvars_4999_);
lean_dec(v_expectedType_x3f_4998_);
lean_dec(v_body_4997_);
lean_dec_ref(v_decls_4995_);
v_a_5041_ = lean_ctor_get(v___x_5013_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_5013_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5043_ = v___x_5013_;
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v___x_5013_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
else
{
lean_object* v_a_5049_; lean_object* v___x_5051_; uint8_t v_isShared_5052_; uint8_t v_isSharedCheck_5056_; 
lean_dec_ref(v_fvars_4999_);
lean_dec(v_expectedType_x3f_4998_);
lean_dec(v_body_4997_);
lean_dec_ref(v_a_4996_);
lean_dec_ref(v_decls_4995_);
v_a_5049_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5051_ = v___x_5012_;
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
else
{
lean_inc(v_a_5049_);
lean_dec(v___x_5012_);
v___x_5051_ = lean_box(0);
v_isShared_5052_ = v_isSharedCheck_5056_;
goto v_resetjp_5050_;
}
v_resetjp_5050_:
{
lean_object* v___x_5054_; 
if (v_isShared_5052_ == 0)
{
v___x_5054_ = v___x_5051_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_a_5049_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___lam__0___boxed(lean_object* v_decls_5057_, lean_object* v_a_5058_, lean_object* v_body_5059_, lean_object* v_expectedType_x3f_5060_, lean_object* v_fvars_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l_Lean_Elab_Term_elabLetRec___lam__0(v_decls_5057_, v_a_5058_, v_body_5059_, v_expectedType_x3f_5060_, v_fvars_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_);
lean_dec(v___y_5067_);
lean_dec_ref(v___y_5066_);
lean_dec(v___y_5065_);
lean_dec_ref(v___y_5064_);
lean_dec(v___y_5063_);
lean_dec_ref(v___y_5062_);
return v_res_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec(lean_object* v_stx_5070_, lean_object* v_expectedType_x3f_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_){
_start:
{
lean_object* v___x_5079_; 
v___x_5079_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_mkLetRecDeclView(v_stx_5070_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v_decls_5081_; lean_object* v_body_5082_; lean_object* v___f_5083_; lean_object* v___x_5084_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref(v___x_5079_);
v_decls_5081_ = lean_ctor_get(v_a_5080_, 0);
lean_inc_ref_n(v_decls_5081_, 2);
v_body_5082_ = lean_ctor_get(v_a_5080_, 1);
lean_inc(v_body_5082_);
v___f_5083_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetRec___lam__0___boxed), 12, 4);
lean_closure_set(v___f_5083_, 0, v_decls_5081_);
lean_closure_set(v___f_5083_, 1, v_a_5080_);
lean_closure_set(v___f_5083_, 2, v_body_5082_);
lean_closure_set(v___f_5083_, 3, v_expectedType_x3f_5071_);
v___x_5084_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_withAuxLocalDecls___redArg(v_decls_5081_, v___f_5083_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_);
return v___x_5084_;
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec(v_expectedType_x3f_5071_);
v_a_5085_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5079_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5079_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabLetRec___boxed(lean_object* v_stx_5093_, lean_object* v_expectedType_x3f_5094_, lean_object* v_a_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l_Lean_Elab_Term_elabLetRec(v_stx_5093_, v_expectedType_x3f_5094_, v_a_5095_, v_a_5096_, v_a_5097_, v_a_5098_, v_a_5099_, v_a_5100_);
lean_dec(v_a_5100_);
lean_dec_ref(v_a_5099_);
lean_dec(v_a_5098_);
lean_dec_ref(v_a_5097_);
lean_dec(v_a_5096_);
lean_dec_ref(v_a_5095_);
lean_dec(v_stx_5093_);
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1(){
_start:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5116_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5117_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__1));
v___x_5118_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3));
v___x_5119_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLetRec___boxed), 9, 0);
v___x_5120_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5116_, v___x_5117_, v___x_5118_, v___x_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___boxed(lean_object* v_a_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1();
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3(){
_start:
{
lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5149_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec__1___closed__3));
v___x_5150_ = ((lean_object*)(l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___closed__6));
v___x_5151_ = l_Lean_addBuiltinDeclarationRanges(v___x_5149_, v___x_5150_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3___boxed(lean_object* v_a_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l___private_Lean_Elab_LetRec_0__Lean_Elab_Term_elabLetRec___regBuiltin_Lean_Elab_Term_elabLetRec_declRange__3();
return v_res_5153_;
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
